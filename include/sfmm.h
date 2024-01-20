/**
 * === DO NOT MODIFY THIS FILE ===
 * If you need some other prototypes or constants in a header, please put them
 * in another header file.
 *
 * When we grade, we will be replacing this file with our own copy.
 * You have been warned.
 * === DO NOT MODIFY THIS FILE ===
 */
#ifndef SFMM_H
#define SFMM_H
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/*

                                 Format of an allocated memory block
    +-----------------------------------------------------------------------------------------+
    |                                    64-bit-wide row                                      |
    +-----------------------------------------------------------------------------------------+

    +----------------------------+-------------------------------+--------+---------+---------+ <- header
    |      payload_size          |          block_size           | alloc  |prv alloc| unused  |
    |                            |     (4 LSB's implicitly 0)    |  (1)   |  (0/1)  |   (0)   |
    |       (32 bits)            |           (28 bits)           | 1 bit  |  1 bit  |  2 bits |
    +----------------------------+-------------------------------+--------+---------+---------+ <- (aligned)
    |                                                                                         |
    |                                   Payload and Padding                                   |
    |                                        (N rows)                                         |
    |                                                                                         |
    |                                                                                         |
    +----------------------------+-------------------------------+--------+---------+---------+ <- footer
    |       payload_size         |          block_size           | alloc  |prv alloc|  unused |
    |                            |     (4 LSB's implicitly 0)    |  (1)   |  (0/1)  |   (0)   |
    |        (32 bits)           |          (28 bits)            | 1 bit  |  1 bit  |  2 bits |
    +----------------------------+-------------------------------+--------+---------+---------+

    NOTE: Footer contents must always be identical to header contents.
*/

/*
                                     Format of a free memory block

    +----------------------------+-------------------------------+--------+---------+---------+ <- header
    |         unused             |          block_size           | alloc  |prv alloc| unused  |
    |          (0)               |     (4 LSB's implicitly 0)    |  (0)   |  (0/1)  |   (0)   |
    |        (32 bits)           |          (28 bits)            | 1 bit  |  1 bit  |  2 bits |
    +----------------------------+-------------------------------+--------+---------+---------+ <- (aligned)
    |                                                                                         |
    |                                Pointer to next free block                               |
    |                                        (1 row)                                          |
    +-----------------------------------------------------------------------------------------+
    |                                                                                         |
    |                               Pointer to previous free block                            |
    |                                        (1 row)                                          |
    +-----------------------------------------------------------------------------------------+
    |                                                                                         | 
    |                                         Unused                                          | 
    |                                        (N rows)                                         |
    |                                                                                         |
    |                                                                                         |
    +------------------------------------------------------------+--------+---------+---------+ <- footer
    |         unused             |          block_size           | alloc  |prv alloc| unused  |
    |          (0)               |     (4 LSB's implicitly 0)    |  (0)   |  (0/1)  |   (0)   |
    |        (32 bits)           |          (28 bits)            | 1 bit  |  1 bit  |  1 bit  |
    +----------------------------+-------------------------------+--------+---------+---------+

    NOTE: Footer contents must always be identical to header contents.
*/

typedef size_t sf_header;
typedef size_t sf_footer;

/*
 * Structure of a block.
 * The first field of this structure is actually the footer of the *previous* block.
 * This must be taken into account when creating sf_block pointers from memory addresses.
 */
typedef struct sf_block {
    sf_footer prev_footer;  // NOTE: This actually belongs to the *previous* block.
    sf_header header;       // This is where the current block really starts.
    union {
        /* A free block contains links to other blocks in a free list. */
        struct {
            struct sf_block *next;
            struct sf_block *prev;
        } links;
        /* An allocated block contains a payload (aligned), starting here. */
        char payload[0];   // Length varies according to block size.
    } body;
} sf_block;

/*
 * The heap is designed to keep the payload area of each block aligned to a two-row (16-byte)
 * boundary.  The header of a block precedes the payload area, and is only single-row (8-byte)
 * aligned.  The first block of the heap starts as soon as possible after the beginning of the
 * heap, subject to the condition that its payload area is two-row aligned.
 */

/*
                                         Format of the heap
    +-----------------------------------------------------------------------------------------+
    |                                    64-bit-wide row                                      |
    +-----------------------------------------------------------------------------------------+

    +-----------------------------------------------------------------------------------------+ <- heap start
    |                                                                                         |    (aligned)
    |                                        Unused                                           |
    |                                       (1 rows)                                          |
    +----------------------------+-------------------------------+--------+---------+---------+ <- header
    |         unused             |          block_size           | alloc  |  unused | unused  |
    |          (0)               |     (4 LSB's implicitly 0)    |  (1)   |   (0)   |   (0)   | prologue
    |        (32 bits)           |          (28 bits)            | 1 bit  |  1 bit  |  2 bits |
    +----------------------------+-------------------------------+--------+---------+---------+ <- (aligned)
    |                                                                                         |
    |                                        Padding                                          |
    |                                 (to minimum block size)                                 |
    |                                                                                         |
    |                                                                                         |
    +----------------------------+-------------------------------+--------+---------+---------+ <- footer
    |         unused             |          block_size           | alloc  |  unused | unused  |
    |          (0)               |     (4 LSB's implicitly 0)    |  (1)   |   (0)   |   (0)   |
    |        (32 bits)           |          (28 bits)            | 1 bit  |  1 bit  |  2 bits |
    +----------------------------+-------------------------------+--------+---------+---------+ <- header
    |       payload_size         |          block_size           | alloc  |prv alloc| unused  |
    |                            |     (4 LSB's implicitly 0)    | (0/1)  |  (0/1)  |   (0)   | first block
    |        (32 bits)           |          (28 bits)            | 1 bit  |  1 bit  |  2 bits |
    +----------------------------+-------------------------------+--------+---------+---------+ <- (aligned)
    |                                                                                         |
    |                                   Payload and Padding                                   |
    |                                        (N rows)                                         |
    |                                                                                         |
    |                                                                                         |
    +----------------------------+-------------------------------+--------+---------+---------+ <- footer
    |       payload_size         |          block_size           | alloc  |prv alloc| unused  |
    |                            |     (4 LSB's implicitly 0)    |  (0/1) |  (0/1)  |   (0)   |
    |        (32 bits)           |          (28 bits)            | 1 bit  |  1 bit  |  2 bits |
    +----------------------------+-------------------------------+--------+---------+---------+
    |                                                                                         |
    |                                                                                         |
    |                                                                                         |
    |                                                                                         |
    |                             Additional allocated and free blocks                        |
    |                                                                                         |
    |                                                                                         |
    |                                                                                         |
    +----------------------------+-------------------------------+--------+---------+---------+ <- header
    |         unused             |          unused               | alloc  |prv alloc| unused  |
    |                            |                               |  (1)   |  (0/1)  |   (0)   | epilogue
    |        (32 bits)           |          (28 bits)            | 1 bit  |  1 bit  |  2 bits |
    +----------------------------+-------------------------------+--------+---------+---------+ <- heap end
                                                                                                   (aligned)
*/

/* sf_errno: will be set on error */
int sf_errno;

/*
 * Free blocks are maintained in a set of circular, doubly linked lists, segregated by
 * size class.  The sizes increase according to a Fibonacci sequence (1, 2, 3, 5, 8, 13, ...).
 * The first list holds blocks of the minimum size M.  The second list holds blocks of size 2M.
 * The third list holds blocks of size 3M.  The fourth list holds blocks whose size is in the
 * interval (3M, 5M].  The fifth list holds blocks whose size is in the interval (5M, 8M],
 * and so on.  This continues up to the list at index NUM_FREE_LISTS-2 (i.e. 8), which
 * contains blocks whose size is greater than 34M.  The last list (at index NUM_FREE_LISTS-1;
 * i.e. 9) is only used to contain the so-called "wilderness block", which is the free block
 * at the end of the heap that will be extended when the heap is grown.
 *
 * Each of the circular, doubly linked lists has a "dummy" block used as the list header.
 * This dummy block is always linked between the last and the first element of the list.
 * In an empty list, the next and free pointers of the list header point back to itself.
 * In a list with something in it, the next pointer of the header points to the first node
 * in the list and the previous pointer of the header points to the last node in the list.
 * The header itself is never removed from the list and it contains no data (only the link
 * fields are used).  The reason for doing things this way is to avoid edge cases in insertion
 * and deletion of nodes from the list.
 */

#define NUM_FREE_LISTS 10
struct sf_block sf_free_list_heads[NUM_FREE_LISTS];

/*
 * This is your implementation of sf_malloc. It acquires uninitialized memory that
 * is aligned and padded properly for the underlying system.
 *
 * @param size The number of bytes requested to be allocated.
 *
 * @return If size is 0, then NULL is returned without setting sf_errno.
 * If size is nonzero, then if the allocation is successful a pointer to a valid region of
 * memory of the requested size is returned.  If the allocation is not successful, then
 * NULL is returned and sf_errno is set to ENOMEM.
 */
void *sf_malloc(size_t size);

/*
 * Resizes the memory pointed to by ptr to size bytes.
 *
 * @param ptr Address of the memory region to resize.
 * @param size The minimum size to resize the memory to.
 *
 * @return If successful, the pointer to a valid region of memory is
 * returned, else NULL is returned and sf_errno is set appropriately.
 *
 *   If sf_realloc is called with an invalid pointer sf_errno should be set to EINVAL.
 *   If there is no memory available sf_realloc should set sf_errno to ENOMEM.
 *
 * If sf_realloc is called with a valid pointer and a size of 0 it should free
 * the allocated block and return NULL without setting sf_errno.
 */
void *sf_realloc(void *ptr, size_t size);

/*
 * Marks a dynamically allocated region as no longer in use.
 * Adds the newly freed block to the free list.
 *
 * @param ptr Address of memory returned by the function sf_malloc.
 *
 * If ptr is invalid, the function calls abort() to exit the program.
 */
void sf_free(void *ptr);

/*
 * Get the current amount of internal fragmentation of the heap.
 *
 * @return  the current amount of internal fragmentation, defined to be the
 * ratio of the total amount of payload to the total size of allocated blocks.
 * If there are no allocated blocks, then the returned value should be 0.0.
 */
double sf_fragmentation();

/*
 * Get the peak memory utilization for the heap.
 *
 * @return  the peak memory utilization over the interval starting from the
 * time the heap was initialized, up to the current time.  The peak memory
 * utilization at a given time, as defined in the lecture and textbook,
 * is the ratio of the maximum aggregate payload up to that time, divided
 * by the current heap size.  If the heap has not yet been initialized,
 * this function should return 0.0.
 */
double sf_utilization();


/* sfutil.c: Helper functions already created for this assignment. */

/*
 * @return The starting address of the heap for your allocator.
 */
void *sf_mem_start();

/*
 * @return The ending address of the heap for your allocator.
 */
void *sf_mem_end();

/*
 * This function increases the size of your heap by adding one page of
 * memory to the end.
 *
 * @return On success, this function returns a pointer to the start of the
 * additional page, which is the same as the value that would have been returned
 * by get_heap_end() before the size increase.  On error, NULL is returned.
 */
void *sf_mem_grow();

/* The size of a page of memory returned by sf_mem_grow(). */
#define PAGE_SZ ((size_t)4096)

/*
 * Display the contents of the heap in a human-readable form.
 */
void sf_show_block(sf_block *bp);
void sf_show_blocks();
void sf_show_free_list(int index);
void sf_show_free_lists();
void sf_show_heap();

#endif
