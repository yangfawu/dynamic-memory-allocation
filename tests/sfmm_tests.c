#include <criterion/criterion.h>
#include <errno.h>
#include <signal.h>
#include "debug.h"
#include "sfmm.h"
#define TEST_TIMEOUT 15

/*
 * Assert the total number of free blocks of a specified size.
 * If size == 0, then assert the total number of all free blocks.
 */
void assert_free_block_count(size_t size, int count) {
    int cnt = 0;
    for(int i = 0; i < NUM_FREE_LISTS; i++) {
	sf_block *bp = sf_free_list_heads[i].body.links.next;
	while(bp != &sf_free_list_heads[i]) {
	    if(size == 0 || size == (bp->header & ~0xf))
		cnt++;
	    bp = bp->body.links.next;
	}
    }
    if(size == 0) {
	cr_assert_eq(cnt, count, "Wrong number of free blocks (exp=%d, found=%d)",
		     count, cnt);
    } else {
	cr_assert_eq(cnt, count, "Wrong number of free blocks of size %ld (exp=%d, found=%d)",
		     size, count, cnt);
    }
}

/*
 * Assert that the free list with a specified index has the specified number of
 * blocks in it.
 */
void assert_free_list_size(int index, int size) {
    int cnt = 0;
    sf_block *bp = sf_free_list_heads[index].body.links.next;
    while(bp != &sf_free_list_heads[index]) {
	cnt++;
	bp = bp->body.links.next;
    }
    cr_assert_eq(cnt, size, "Free list %d has wrong number of free blocks (exp=%d, found=%d)",
		 index, size, cnt);
}

Test(sfmm_basecode_suite, malloc_an_int, .timeout = TEST_TIMEOUT) {
	sf_errno = 0;
	int *x = sf_malloc(sizeof(int));

	cr_assert_not_null(x, "x is NULL!");

	*x = 4;

	cr_assert(*x == 4, "sf_malloc failed to give proper space for an int!");

	assert_free_block_count(0, 1);
	assert_free_block_count(4016, 1);
	assert_free_list_size(9, 1);

	cr_assert(sf_errno == 0, "sf_errno is not zero!");
	cr_assert(sf_mem_start() + PAGE_SZ == sf_mem_end(), "Allocated more than necessary!");
}

Test(sfmm_basecode_suite, malloc_four_pages, .timeout = TEST_TIMEOUT) {
	sf_errno = 0;
	// We want to allocate up to exactly four pages.
	void *x = sf_malloc(16384 - 48 - (sizeof(sf_header) + sizeof(sf_footer)));

	cr_assert_not_null(x, "x is NULL!");
	assert_free_block_count(0, 0);
	cr_assert(sf_errno == 0, "sf_errno is not 0!");
}

Test(sfmm_basecode_suite, malloc_too_large, .timeout = TEST_TIMEOUT) {
	sf_errno = 0;
	void *x = sf_malloc(PAGE_SZ << 16);

	cr_assert_null(x, "x is not NULL!");
	assert_free_block_count(0, 1);
	assert_free_block_count(110544, 1);
	cr_assert(sf_errno == ENOMEM, "sf_errno is not ENOMEM!");
}

Test(sfmm_basecode_suite, free_no_coalesce, .timeout = TEST_TIMEOUT) {
	sf_errno = 0;
	/* void *x = */ sf_malloc(8);
	void *y = sf_malloc(200);
	/* void *z = */ sf_malloc(1);

	sf_free(y);

	assert_free_block_count(0, 2);
	assert_free_block_count(224, 1);
	assert_free_block_count(3760, 1);
	cr_assert(sf_errno == 0, "sf_errno is not zero!");
}

Test(sfmm_basecode_suite, free_coalesce, .timeout = TEST_TIMEOUT) {
	sf_errno = 0;
	/* void *w = */ sf_malloc(8);
	void *x = sf_malloc(200);
	void *y = sf_malloc(300);
	/* void *z = */ sf_malloc(4);

	sf_free(y);
	sf_free(x);

	assert_free_block_count(0, 2);
	assert_free_block_count(544, 1);
	assert_free_block_count(3440, 1);
	cr_assert(sf_errno == 0, "sf_errno is not zero!");
}

Test(sfmm_basecode_suite, freelist, .timeout = TEST_TIMEOUT) {
	void *u = sf_malloc(200);
	/* void *v = */ sf_malloc(300);
	void *w = sf_malloc(200);
	/* void *x = */ sf_malloc(500);
	void *y = sf_malloc(200);
	/* void *z = */ sf_malloc(700);

	sf_free(u);
	sf_free(w);
	sf_free(y);

	assert_free_block_count(0, 4);
	assert_free_block_count(224, 3);
	assert_free_block_count(1808, 1);
	assert_free_list_size(4, 3);
	assert_free_list_size(9, 1);

	// First block in list should be the most recently freed block.
	int i = 4;
	sf_block *bp = sf_free_list_heads[i].body.links.next;
	cr_assert_eq(bp, (char *)y - 2*sizeof(sf_header),
		     "Wrong first block in free list %d: (found=%p, exp=%p)!",
                     i, bp, (char *)y - 2*sizeof(sf_header));
}

Test(sfmm_basecode_suite, realloc_larger_block, .timeout = TEST_TIMEOUT) {
	void *x = sf_malloc(sizeof(int));
	/* void *y = */ sf_malloc(10);
	x = sf_realloc(x, sizeof(int) * 20);

	cr_assert_not_null(x, "x is NULL!");
	sf_block *bp = (sf_block *)((char *)x - 2*sizeof(sf_header));
	cr_assert(bp->header & 0x8, "Allocated bit is not set!");
	cr_assert((bp->header & ~0xf & 0xffff) == 96,
		  "Realloc'ed block size not what was expected (found=%lu, exp=%lu)!",
		  bp->header & ~0xf, 96);

	assert_free_block_count(0, 2);
	assert_free_block_count(32, 1);
	assert_free_block_count(3888, 1);
}

Test(sfmm_basecode_suite, realloc_smaller_block_splinter, .timeout = TEST_TIMEOUT) {
	void *x = sf_malloc(sizeof(int) * 20);
	void *y = sf_realloc(x, sizeof(int) * 16);

	cr_assert_not_null(y, "y is NULL!");
	cr_assert(x == y, "Payload addresses are different!");

	sf_block *bp = (sf_block *)((char*)y - 2*sizeof(sf_header));
	cr_assert(bp->header & 0x8, "Allocated bit is not set!");
	cr_assert((bp->header & ~0xf & 0xffff) == 96,
		  "Block size not what was expected (found=%lu, exp=%lu)!",
		  bp->header & ~0xf & 0xffff, 96);

	// There should be only one free block of size 3952.
	assert_free_block_count(0, 1);
	assert_free_block_count(3952, 1);
}

Test(sfmm_basecode_suite, realloc_smaller_block_free_block, .timeout = TEST_TIMEOUT) {
	void *x = sf_malloc(sizeof(double) * 8);
	void *y = sf_realloc(x, sizeof(int));

	cr_assert_not_null(y, "y is NULL!");

	sf_block *bp = (sf_block *)((char*)y - 2*sizeof(sf_header));
	cr_assert(bp->header & 0x8, "Allocated bit is not set!");
	cr_assert((bp->header & ~0xf & 0xffff) == 32,
		  "Realloc'ed block size not what was expected (found=%lu, exp=%lu)!",
		  bp->header & ~0xf & 0xffff, 32);

	// After realloc'ing x, we can return a block of size 32 to the freelist.
	// This block will go into the freelist and be coalesced.
	assert_free_block_count(0, 1);
	assert_free_block_count(4016, 1);
}

//############################################
//STUDENT UNIT TESTS SHOULD BE WRITTEN BELOW
//DO NOT DELETE THESE COMMENTS
//############################################

Test(sfmm_student_suite, malloc_last_block, .timeout = TEST_TIMEOUT) {
	// creates a block of size 32
	// produces a remainder block of size 4016
	sf_malloc(16);

	// creates a block of size 4016
    sf_malloc(4000);

    // there should be no blocks in any of the free list
    for (int i=0; i<NUM_FREE_LISTS; i++)
    	assert_free_list_size(i, 0);

    // check that the epilogue also has the prev_alloc set
    sf_header* ep = (sf_header*)((char*)sf_mem_end() - 8);
    cr_assert((*ep & 0x4) == 0x4, "Previous-allocated bit in epilogue is not set");
}

Test(sfmm_student_suite, realloc_and_get_same_ptr, .timeout = TEST_TIMEOUT) {
	void* x = sf_malloc(16);

	// realloc into a smaller payload size, but the block size should still be the same
	// so the pointer should still be at the same block
	void* y = sf_realloc(x, 8);
	cr_assert(x == y, "Pointer should not have changed");

	// realloc into a bigger payload size, but the block size should remain the same
	// so the block pointer should not change whatsoever
	void* z = sf_realloc(y, 16);
	cr_assert(y == z, "Pointer should not have changed");
	cr_assert(x == z, "Pointer should not have changed");
}

Test(sfmm_student_suite, free_ptr_twice, .timeout = TEST_TIMEOUT, .signal = SIGABRT) {
	void* x = sf_malloc(16);
	sf_free(x);

	// this should cause the test case to abort
	sf_free(x);
}

Test(sfmm_student_suite, free_invalid, .timeout = TEST_TIMEOUT, .signal = SIGABRT) {
	void* x = sf_malloc(16);

	// move the pointer to somewhere illegal
	void* y = (void*)((char*)x - 5);

	// freeing with this address should cause an abort
	sf_free(y);
}

Test(sfmm_student_suite, realloc_invalid, .timeout = TEST_TIMEOUT) {
	void* x = sf_malloc(16);

	// move the pointer to somewhere illegal
	void* y = (void*)((char*)x - 5);

	// attempt to realloc this new pointer
	void* z = sf_realloc(y, 16);
	cr_assert(z == NULL, "Pointer should be NULL due to being invalid");
	cr_assert(sf_errno == EINVAL, "sf_errno should indicate an invalid value");
}
