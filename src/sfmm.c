/**
 * Do not submit your assignment with a main function in this file.
 * If you submit with a main function in this file, you will get a zero.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "sfmm.h"

#include <errno.h> // added for ENOMEM

typedef unsigned int uint;

#define ALIGNMENT_SIZE ((size_t)16)

#define WORD_SIZE ((size_t)2)

#define ROW_SIZE (4*WORD_SIZE)

#define M (4*ROW_SIZE)

#define BLOCK_SIZE_MASK ((size_t)0xfffffff0)

#define BLOCK_FLAGS_MASK ((size_t)0xc)

#define CURR_ALLOC_FLAG ((size_t)0x8)

#define PREV_ALLOC_FLAG ((size_t)0x4)

static uint heap_initialized = 0;

/**
 * Running totals used for later memory analysis functions
 */
static size_t total_payload_size = 0;
static size_t max_total_payload_size = 0;
static size_t total_allocated_block_size = 0;

static void incr_total_payload_size(size_t amt) {
    total_payload_size+= amt;
    if (total_payload_size > max_total_payload_size)
        max_total_payload_size = total_payload_size;
}

// we do this to ensure the static cache is initialized with 0s
#if NUM_FREE_LISTS < 3
static size_t fib(uint i) {
    // this should never be called
    abort();
}
#else
// we do not need to compute fib for list indices after third to last list
// we include support for second to last list even though it is not needed because it will break our cache size
static size_t fibonacci_cache[NUM_FREE_LISTS-1] = { 1, 2 };
static size_t fib(uint i) {
    if (fibonacci_cache[i] == 0)
        fibonacci_cache[i] = fib(i-1) + fib(i-2);
    return fibonacci_cache[i];
}
#endif

static size_t get_payload_size(sf_block* bp) {
    return bp->header >> 32;
}

static size_t get_block_size(sf_block* bp) {
    return bp->header & BLOCK_SIZE_MASK;
}

static size_t get_block_flags(sf_block* bp) {
    return bp->header & BLOCK_FLAGS_MASK;
}

static size_t build_meta_row(size_t payload_size, size_t block_size, size_t block_flags) {
    return (payload_size << 32) | (block_size & BLOCK_SIZE_MASK) | (block_flags & BLOCK_FLAGS_MASK);
}

static sf_block* next_block(sf_block* bp) {
    return (sf_block*)((char*)bp + get_block_size(bp));
}

static sf_block* prev_block(sf_block* bp) {
    return (sf_block*)((char*)bp - (bp->prev_footer & BLOCK_SIZE_MASK));
}

static sf_footer* get_footer(sf_block* bp) {
    return (sf_footer*)((char*)next_block(bp));
}

static sf_header* get_epilogue() {
    return (sf_header*)((char*)sf_mem_end() - ROW_SIZE);
}

static sf_block* get_bp_from_body_p(void* pp) {
    return (sf_block*)((char*)pp - 2*ROW_SIZE);
}

/**
 * Inserts block at specified list indx
 */
static void insert_block_into_list(uint i, sf_block* bp) {
    sf_block* sentinel_bp = sf_free_list_heads + i;
    sf_block* after_sentinel_bp = sentinel_bp->body.links.next;

    sentinel_bp->body.links.next = bp;
    bp->body.links.prev = sentinel_bp;
    bp->body.links.next = after_sentinel_bp;
    after_sentinel_bp->body.links.prev = bp;
}

/**
 * Takes a block pointer and inserts it at the start of the appropiate free list
 */
static void insert_block(sf_block* bp) {
    // if this block is the last one on the heap, we add it to the special at the end
    // it doesn't matter how small it is
    if ((char*)get_footer(bp) == (char*)get_epilogue() - ROW_SIZE) {
        insert_block_into_list(NUM_FREE_LISTS - 1, bp);
        return;
    }

    uint head_index = NUM_FREE_LISTS - 2; // default list set to second to last list
    size_t block_size = get_block_size(bp);
    for (uint i=0; i<NUM_FREE_LISTS-1; i++) {
        // check upper limit only if list is not second to last list
        if (i < NUM_FREE_LISTS-2 && block_size > fib(i)*M)
            continue;
        head_index = i;
        break;
    }
    insert_block_into_list(head_index, bp);
}

/**
 * Takes a (assumed free) block and removes it from its free list
 */
static void remove_block(sf_block* bp) {
    sf_block* before_bp = bp->body.links.prev;
    sf_block* after_bp = bp->body.links.next;

    before_bp->body.links.next = after_bp;
    after_bp->body.links.prev = before_bp;

    bp->body.links.next = NULL;
    bp->body.links.prev = NULL;
}

/**
 * Initializes the free lists and extend the heap for our first free block
 * Uses a static variable to ensure that this only happens on first malloc call
 * Returns 0 if successful
 * Returns -1 if otherwise
 */
static int init_heap() {
    static int result = 1; // cache result after initialization
    if (heap_initialized)
        return result;

    // init free list heads
    sf_block* sentinel_bp = sf_free_list_heads;
    for (uint i=0; i<NUM_FREE_LISTS; i++, sentinel_bp++) {
        sentinel_bp->body.links.next = sentinel_bp;
        sentinel_bp->body.links.prev = sentinel_bp;
    }

    // sf_mem_grow actually returns address of unused row
    // but the struct is organized to have the previous row (in this case, the unused row)
    sf_block* prologue = (sf_block*) sf_mem_grow();
    if (prologue == NULL)
        return (result = -1);

    prologue->header = build_meta_row(0, M, CURR_ALLOC_FLAG);

    *get_epilogue() = build_meta_row(0, 0, CURR_ALLOC_FLAG);

    // get wild block by adding M bytes to prologue's address
    // the address free block will actually start at prologue's footer
    sf_block* wild_block = next_block(prologue);
    wild_block->prev_footer = prologue->header;

    // we can compute wild block's size by subtracting pad row, prologue, and epilogue from PAGE_SZ
    wild_block->header = build_meta_row(0, PAGE_SZ - M - 2*ROW_SIZE, PREV_ALLOC_FLAG);
    *get_footer(wild_block) = wild_block->header;

    insert_block_into_list(NUM_FREE_LISTS - 1, wild_block);

    heap_initialized = 1;
    return (result = 0);
}

/**
 * Takes a payload size and adjusts it to fit a header, a footer, 2 pointers, and be aligned
 */
static size_t adjust(size_t size) {
    // check if the requested payload size can fit the previous and next pointers
    if (size < 2*ROW_SIZE)
        return M; // if not, we use the minimally acceptable size

    // if we can, then we just add the bytes needed for a header and footer
    size_t new_size = size + 2*ROW_SIZE;

    // align new_size if needed
    if (new_size % ALIGNMENT_SIZE)
        return (new_size + ALIGNMENT_SIZE)/ALIGNMENT_SIZE*ALIGNMENT_SIZE;
    return new_size;
}

/**
 * Given a target size, finds the first fitting block in the appropiate free list.
 * Will also remove the block from its free list in the process.
 */
static sf_block* find_candidate_block(size_t target_block_size) {
    sf_block* head = sf_free_list_heads;
    sf_block* curr_bp;
    for (uint i=0; i<NUM_FREE_LISTS; i++, head++) {
        // check if target size fits within current list's upper limit
        // NOTE: there is no limit on last list (the list before wild list)
        if (i < NUM_FREE_LISTS - 2 && target_block_size > fib(i)*M)
            continue;

        // search for first block that fits
        curr_bp = head;
        while ((curr_bp = curr_bp->body.links.next) != head) {
            if (target_block_size > get_block_size(curr_bp))
                continue;

            remove_block(curr_bp);
            return curr_bp;
        }
    }
    return NULL;
}

/**
 * Attempts to coalesce the current block with previous free blocks until no more is found
 * Assumes the current block is free and is NOT in the free list
 * Assumes the previous free blocks are in the free list
 * Returns a truly left-coalesced free block NOT in the free list
 */
static sf_block* left_coalesce(sf_block* bp) {
    // if the previous block is allocated, we can stop at bp
    if ((get_block_flags(bp) & PREV_ALLOC_FLAG) == PREV_ALLOC_FLAG)
        return bp;

    // update previous block to absorb this block
    sf_block* prev_bp = prev_block(bp);
    prev_bp->header = build_meta_row(
        0,
        get_block_size(prev_bp) + get_block_size(bp),
        get_block_flags(prev_bp) // preserve flags
    );
    *get_footer(bp) = prev_bp->header;

    // remove the previous block from its current list before coalescing again
    remove_block(prev_bp);
    return left_coalesce(prev_bp);
}

/**
 * Attempts to coalesce all free blocks following this block into this block
 * Assumes the current block is free and is NOT in the free list
 * Assumes the following free blocks are in the free list
 */
static void right_coalesce(sf_block* bp) {
    // compute the impossible block address
    char* illegal_bp = (char*)get_epilogue() - ROW_SIZE;

    size_t curr_size = get_block_size(bp);

    // look at blocks on the right all the way to epilogue if needed
    sf_block* curr_bp = bp;
    while ((char*)(curr_bp = next_block(curr_bp)) != illegal_bp) {
        // ensure that this new block is not already being used
        if ((get_block_flags(curr_bp) & CURR_ALLOC_FLAG) == CURR_ALLOC_FLAG)
            break;

        // gobble up block and remove it from its free list
        curr_size+= get_block_size(curr_bp);
        remove_block(curr_bp);
    }

    // if we did not consume any blocks, no need to update block
    if (curr_size == get_block_size(bp))
        return;

    // otherwise update block information
    bp->header = build_meta_row(
        0,
        curr_size,
        get_block_flags(bp) // preserve current block's flags
    );
    *get_footer(bp) = bp->header;
}

/**
 * Attempts to completely coalesce this block with all free blocks surrounding it
 * Assumes the current block is free and is NOT in a free list
 * Will return the leftmost free block in the chain
 */
static sf_block* coalesce(sf_block* bp) {
    right_coalesce(bp);
    return left_coalesce(bp);
}

/**
 * Given a target block size, it will extend the heap as much as possible to fit it
 * It will also check if it can start at where the wilderness block ended at the epilogue
 * It will modify the block pointer if such block is found and return 0
 * If not, it will return -1
 */
static int create_block_from_heap(size_t target_block_size, sf_block** bp_p) {
    char* old_ep = (char*)get_epilogue();

    // if the last block in heap is free, we start with its size knowing that we will coalesce into it later
    sf_footer* last_block_footer = (sf_footer*)(old_ep - ROW_SIZE);
    size_t curr_size = (*last_block_footer & CURR_ALLOC_FLAG) != CURR_ALLOC_FLAG ?
        *last_block_footer & BLOCK_SIZE_MASK :
        0;

    // expand our heap as much as possible
    // NOTE: we can exit while loop before hitting target
    size_t new_block_size = 0;
    while (curr_size < target_block_size) {
        if (sf_mem_grow() == NULL)
            break;
        curr_size+= PAGE_SZ;
        new_block_size+= PAGE_SZ;
    }

    // check if we even managed to expand the heap at all
    if (new_block_size == 0)
        return -1;

    // update epilogue
    *get_epilogue() = build_meta_row(0, 0, CURR_ALLOC_FLAG);

    // build new block
    sf_block* new_bp = (sf_block*)(old_ep - ROW_SIZE);
    new_bp->header = build_meta_row(
        0,
        new_block_size,
        // use previous block's alloc flag to set our prev_alloc
        (new_bp->prev_footer & CURR_ALLOC_FLAG) == CURR_ALLOC_FLAG ? PREV_ALLOC_FLAG : 0
    );
    *get_footer(new_bp) = new_bp->header;

    // coalesce new block with previous blocks if possible
    new_bp = left_coalesce(new_bp);

    // store block in free list if we did not manage to obtain a block that satisfies the requirements
    if (get_block_size(new_bp) < target_block_size) {
        insert_block(new_bp);
        return -1;
    }

    *bp_p = new_bp;
    return 0;
}

/**
 * Takes a block and split off the remainder
 * Assumes the current block will be used for allocation
 * Assumes splinter is not possible
 */
static void split_block(sf_block* bp, size_t remainder_size) {
    sf_block *remainder_bp = next_block(bp);
    remainder_bp->prev_footer = bp->header;
    remainder_bp->header = build_meta_row(
        0,
        remainder_size,
        PREV_ALLOC_FLAG
    );
    *get_footer(remainder_bp) = remainder_bp->header;

    // right coalesce the remainder in the next block is free
    // no need to check the left side because it is always allocated
    right_coalesce(remainder_bp);
    insert_block(remainder_bp);
}

void *sf_malloc(size_t size) {
    if (size == 0)
        return NULL;

    // initialize if this is the first malloc call
    if (init_heap()) {
        sf_errno = ENOMEM;
        return NULL;
    }

    size_t adjusted_size = adjust(size);

    sf_block* target_bp = find_candidate_block(adjusted_size);

    // if no candidate found from free list, we turn to the heap
    if (target_bp == NULL && create_block_from_heap(adjusted_size, &target_bp)) {
        sf_errno = ENOMEM;
        return NULL;
    }

    // compute remaining space and split block if no splinter
    size_t new_block_size = get_block_size(target_bp);
    size_t remainder_size = new_block_size - adjusted_size;
    if (remainder_size < M) {
        // splitting will cause a splinter, so we give up entire block to user

        // update payload size and alloc flag
        target_bp->header = build_meta_row(
            size,
            new_block_size,
            get_block_flags(target_bp) | CURR_ALLOC_FLAG
        );

        // update information of block that immediately follows this block
        sf_block* imm_bp = next_block(target_bp);
        imm_bp->prev_footer = target_bp->header;
        imm_bp->header = build_meta_row(
            get_payload_size(imm_bp),
            get_block_size(imm_bp),
            get_block_flags(imm_bp) | PREV_ALLOC_FLAG
        );

        // sometimes this immediate block may end up being the epilogue
        // an epilogue has no footer for us to modify
        if ((char*)imm_bp != (char*)get_epilogue() - ROW_SIZE)
            *get_footer(imm_bp) = imm_bp->header;
    } else {
        // we can split and place remainder block in some list

        // update payload size, block size, and alloc flag
        target_bp->header = build_meta_row(
            size,
            adjusted_size,
            get_block_flags(target_bp) | CURR_ALLOC_FLAG
        );
        split_block(target_bp, remainder_size);
    }

    // update analysis variables
    incr_total_payload_size(get_payload_size(target_bp));
    total_allocated_block_size+= get_block_size(target_bp);
    return &(target_bp->body);
}

/**
 * Takes an external pointer and check if it associated with a valid block
 * If valid block is found, returns 0 and stores block pointer
 * If not, returns non-zero
 */
static int validate_potential_bp(void* pp, sf_block** bp_p) {
    if (pp == NULL)
        return -1;

    // check if address is aligned
    if ((unsigned long int)pp % ALIGNMENT_SIZE)
        return -1;

    sf_block* bp = get_bp_from_body_p(pp);

    // ensure that the address of block does not start before prologue's footer
    if ((char*)bp < (char*)sf_mem_start() + M)
        return -1;

    // ensure that this block is marked as allocated
    if ((get_block_flags(bp) & CURR_ALLOC_FLAG) != CURR_ALLOC_FLAG)
        return -1;

    if ((get_block_flags(bp) & PREV_ALLOC_FLAG) == PREV_ALLOC_FLAG) {
        // if header says previous block is allocated
        // then the alloc flag should be active
        if ((bp->prev_footer & CURR_ALLOC_FLAG) != CURR_ALLOC_FLAG)
            return -1;
    }

    // ensure that the block size is not smaller than min
    // ensure that the block size is aligned
    size_t block_size = get_block_size(bp);
    if (block_size < M || block_size % ALIGNMENT_SIZE)
        return -1;

    // ensure the footer is not at or after the epilogue
    if ((char*)get_footer(bp) >= (char*)get_epilogue())
        return -1;

    *bp_p = bp;
    return 0;
}

/**
 * Takes a real allocated block and free it up
 */
static void free_block(sf_block* bp) {
    // update analysis variables to reflect loss of allocated block
    size_t curr_size = get_block_size(bp);
    total_payload_size-= get_payload_size(bp);
    total_allocated_block_size-= curr_size;

    // update header and footer to indicate free status
    bp->header = build_meta_row(
        0,
        curr_size,
        get_block_flags(bp) & PREV_ALLOC_FLAG // keep only the prev_alloc flag
    );
    *get_footer(bp) = bp->header;

    // coalesce block before inserting back into list
    bp = coalesce(bp);
    insert_block(bp);

    sf_header* ep = get_epilogue();
    if ((char*)get_footer(bp) == (char*)ep - ROW_SIZE) {
        // if coalesced block ends up being the last block, then we just need to update the epilogue
        *ep = build_meta_row(0, 0, CURR_ALLOC_FLAG);
    } else {
        // if coalesced block is not last, we need to notify the immediate block of the allocate status change
        sf_block* imm_bp = next_block(bp);
        imm_bp->header = build_meta_row(
            get_payload_size(imm_bp),
            get_block_size(imm_bp),
            get_block_flags(imm_bp) & ~PREV_ALLOC_FLAG // keep every flag but the prev_alloc flag
        );
        *get_footer(imm_bp) = imm_bp->header;
    }
}

void sf_free(void *pp) {
    sf_block* bp;
    if (validate_potential_bp(pp, &bp))
        abort();
    free_block(bp);
}

void *sf_realloc(void *pp, size_t rsize) {
    sf_block* bp;
    if (validate_potential_bp(pp, &bp)) {
        sf_errno = EINVAL;
        return NULL;
    }

    // check if new size is 0
    if (rsize == 0) {
        // if it is, then the user is no longer using the block
        free_block(bp);
        return NULL;
    }

    // if resizing does not change the size, we don't need to do anything else
    size_t curr_size = get_payload_size(bp);
    if (curr_size == rsize)
        return pp;

    // check if the adjusted block re-size is actually the current block size
    size_t curr_block_size = get_block_size(bp);
    size_t potential_new_block_size = adjust(rsize);
    if (curr_block_size == potential_new_block_size) {
        // if it is, then we don't need to create any new blocks
        // just update the payload bits
        bp->header = build_meta_row(
            rsize,
            curr_block_size,
            get_block_flags(bp)
        );
        *get_footer(bp) = bp->header;

        // update analysis variables to reflect simple payload change
        total_payload_size-= curr_size;
        incr_total_payload_size(rsize);
        return pp;
    }

    // now we know that reallocating will require us to create a new block

    // check if we are reallocating to a larger block
    if (curr_size < rsize) {
        void* new_pp = sf_malloc(rsize);

        // return NULL without changing sf_errno from malloc if we cannot malloc
        if (new_pp == NULL)
            return NULL;

        // otherwise copy memory over to new body pointer
        memcpy(new_pp, pp, curr_size);

        // free old block before returning new pointer
        // NOTE: we free after malloc because memcpy cannot work with overlapping memory
        free_block(bp);
        return new_pp;
    }

    // now we know that we are reallocating to a smaller block
    size_t remainder_size = curr_block_size - potential_new_block_size;
    if (remainder_size < M) {
        // splitting will cause splinter, so we will not split
        // just update the payload bits
        bp->header = build_meta_row(
            rsize,
            curr_block_size,
            get_block_flags(bp)
        );
        *get_footer(bp) = bp->header;

        // update analysis variables to reflect simple payload change
        total_payload_size-= curr_size;
        incr_total_payload_size(rsize);
        return pp;
    }

    // now we know that we can split without splintering
    bp->header = build_meta_row(
        rsize,
        potential_new_block_size,
        get_block_flags(bp)
    );

    // update analysis variables to reflect simple payload change
    total_payload_size-= curr_size;
    incr_total_payload_size(rsize);
    total_allocated_block_size-= curr_block_size;
    total_allocated_block_size+= potential_new_block_size;

    // split off the remainder before giving pointer
    split_block(bp, remainder_size);
    return pp;
}

double sf_fragmentation() {
    if (total_allocated_block_size == 0)
        return 0;
    return (double)total_payload_size/total_allocated_block_size;
}

double sf_utilization() {
    if (!heap_initialized)
        return 0;
    size_t heap_size = (char*)sf_mem_end() - (char*)sf_mem_start();
    return (double)max_total_payload_size/heap_size;
}
