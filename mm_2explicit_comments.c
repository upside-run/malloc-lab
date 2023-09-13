/*********************************************************
 * Explicit free list + first fit
 * Perf index = 44 (util) + 33 (thru) = 78/100
 ********************************************************/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

team_t team = {
    /* Team name */
    "week5-team2",
    /* First member's full name */
    "kai",
    /* First member's email address */
    "kiyoungk_kim@hotmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/*********************************************************
 * Definitions & Function Initialization
 ********************************************************/

#define WSIZE 4         // 4B Word Size
#define DSIZE 8         // 8B Double Word Size (Block Size 16B)
#define INITSIZE 16     // 16B intialization for size of free list before first free block added
#define MINBLOCKSIZE 16 // 8B overahead, 8B for payload or two pointers to next/prev free blocks(4B each)
// INITSIZE & MINBLOCKSIZE added: to make sure code is more readable
// CHUNKSIZE removed: in explicit free list models, heap is dynamically extended as needed

#define ALIGNMENT 8                                     // 8B memory alignment factor
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // round up to multiple of 8 (byte bounary)
#define MAX(x, y) ((x) > (y) ? (x) : (y))               // ternary operator to extract max value
// ALIGNMENT & ALIGN macros added to accomodate various sizes to the block

#define PACK(size, alloc) ((size) | (alloc))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET(p) (*(unsigned int *)(p))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((void *)(bp)-WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((void *)(bp)-GET_SIZE(HDRP(bp) - WSIZE))
// CHAR->VOID: to be more generic in treating data

#define NEXT_FREE(bp) (*(void **)(bp))
#define PREV_FREE(bp) (*(void **)(bp + WSIZE))
// NEXT_FREE & PREV_FREE added: to traverse the free list

static char *heap_listp = 0; // points to the start of the heap (initialized to zero)
static char *free_listp;     // points to the first free block (initialized at mm_init)
static void *extend_heap(size_t words);
static void *find_fit(size_t size);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void remove_freeblock(void *bp); // added to modify freeblock list
// static int mm_check();

/*********************************************************
 * Core Functions of Malloc
 ********************************************************/

int mm_init(void) {
    // Not sure why I get segmentation faults when I assign 24B to mem_sbrk
    // Assuming its due to structure of the simulator, just going to go with 32B

    if ((heap_listp = mem_sbrk(INITSIZE + MINBLOCKSIZE)) == (void *)-1)
        return -1;

    // No Alignment padding, straight to prologue header
    PUT(heap_listp, PACK(WSIZE, 1));                      // 4B Prologue header
    PUT(heap_listp + (1 * WSIZE), PACK(MINBLOCKSIZE, 0)); // 4B free block header
    PUT(heap_listp + (2 * WSIZE), PACK(0, 0));            // 4B payload next pointer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 0));            // 4B payload prev pointer
    PUT(heap_listp + (4 * WSIZE), PACK(MINBLOCKSIZE, 0)); // 4B free block footer
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));            // 4B Epilogue header

    free_listp = heap_listp + (WSIZE); // point to the first header of first free block
    return 0;
}

void *mm_malloc(size_t size) { // identical to implicit mm.c
    if (size == 0)
        return NULL;

    size_t asize = MAX(ALIGN(size) + DSIZE, MINBLOCKSIZE); // Adjusted block size
    size_t extendsize;                                     // Amount to extend heap by if no fit
    char *bp;

    // Search the free list for the fit
    if ((bp = find_fit(asize))) {
        place(bp, asize);
        return bp;
    }

    // Otherwise, no fit was found. Grow the heap larger.
    extendsize = MAX(asize, MINBLOCKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp) { // identical to implicit mm.c
    // Ignore spurious requests (the only addition vs implicit)
    if (!bp)
        return;

    size_t size = GET_SIZE(HDRP(bp)); // get the size of current block
    PUT(HDRP(bp), PACK(size, 0));     // change header to unallocated (0)
    PUT(FTRP(bp), PACK(size, 0));     // change footer to unallocated (0)
    coalesce(bp);                     // now coalsece with adjacent free blocks
}

void *mm_realloc(void *ptr, size_t size) {
    // If ptr is NULL, target block for realloc is not present = mm_malloc(size)
    if (ptr == NULL)
        return mm_malloc(size);
    // If size is equal to zero, realloc is equivalent to mm_free(ptr)
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // Otherwise, we assume ptr is not NULL and was returned by an earlier malloc or realloc call.
    size_t asize = MAX(ALIGN(size) + DSIZE, MINBLOCKSIZE);
    size_t current_size = GET_SIZE(HDRP(ptr)); // size of current block

    void *bp;
    char *next = HDRP(NEXT_BLKP(ptr));              // pointer to header of next block
    size_t newsize = current_size + GET_SIZE(next); // size of current and next block

    // Case 1: Size is equal to the current payload size
    if (asize == current_size)
        return ptr;
    // Case 2: Size is less than the current payload size
    else if (asize <= current_size) {
        // if Size is larger than MIN + if current payload size's remainder is larger than MIN
        if (asize > MINBLOCKSIZE && (current_size - asize) > MINBLOCKSIZE) {
            PUT(HDRP(ptr), PACK(asize, 1)); // temporarily move to header & footer location to claim
            PUT(FTRP(ptr), PACK(asize, 1));
            bp = NEXT_BLKP(ptr);                          // point to where the next block payload should be
            PUT(HDRP(bp), PACK(current_size - asize, 1)); // move to header location and quote the rest
            PUT(FTRP(bp), PACK(current_size - asize, 1));
            mm_free(bp); // free the newly quoted 'bp' block
            return ptr;
        }
        // otherwise, allocate a new block of the requested size and release the current block
        bp = mm_malloc(asize);
        memcpy(bp, ptr, asize);
        mm_free(ptr);
        return bp;
    }
    // Case 3: Requested size is greater than the current payload size
    else {
        // if next block is not allocated + if size of current&next blocks are larger than Size (large enough to complete request)
        if (!GET_ALLOC(next) && newsize >= asize) {
            // merge current&next block, split just the size we need, and release the remainder
            remove_freeblock(NEXT_BLKP(ptr)); // remove from freelist (doubly linked list)
            PUT(HDRP(ptr), PACK(asize, 1));   // claim header and footer for Size
            PUT(FTRP(ptr), PACK(asize, 1));
            bp = NEXT_BLKP(ptr);                     // point to where the next block payload should be
            PUT(HDRP(bp), PACK(newsize - asize, 1)); // claim the remaining size and free it
            PUT(FTRP(bp), PACK(newsize - asize, 1));
            mm_free(bp);
            return ptr;
        }
        // otherwise (if next block is allocated and/or if the size of the block is not big enough)
        // allocate a new block of the requested size and release the current block
        else {
            bp = mm_malloc(asize);
            memcpy(bp, ptr, current_size);
            mm_free(ptr);
            return bp;
        }
    }
}

/*********************************************************
 * Helper functions to support mm_malloc, mm_free, and mm_realloc
 ********************************************************/

static void *extend_heap(size_t words) { // almost identical to implicit mm.c
    char *bp;
    size_t asize;

    // Allocate an even number of words to maintain alignment
    asize = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (asize < MINBLOCKSIZE) // this is probably the only difference to ensure minsize
        asize = MINBLOCKSIZE;

    // if mem_sbrk fails (-1), return NULL
    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    // initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(asize, 0));        // temporarily move bp one WSIZE to enter epilogue header, update new size
    PUT(FTRP(bp), PACK(asize, 0));        // now temporarily move bp to new footer position and update the new size
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // lastly temporarily move bp to where epilogue should be and create it

    // Coalesce any partitioned free memory
    return coalesce(bp);
}

static void *coalesce(void *bp) {                                              // identical to implicit mm.c until case 4
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp; // get footer allocater attribute of previous block
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));                        // get header allocator attribute of next block
    size_t size = GET_SIZE(HDRP(bp));                                          // get size of current block

    // Because this is LIFO, there is no need to consider Case 1 (prev/next allocated)
    // Case 2: prev is allocated and next is free (1, 0)
    if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // increase Size by that of next block
        remove_freeblock(NEXT_BLKP(bp));       // remove the next block and update current header&footer
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // Case 3: prev is free and next is allocated (0, 1)
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // increase Size by that of previous block
        bp = PREV_BLKP(bp);
        remove_freeblock(bp); // remove the previous block and update current header&footer
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // Case 4: both prev and next blocks are free (0, 0)
    else if (!prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_freeblock(PREV_BLKP(bp));
        remove_freeblock(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // (NEW to explicit allocator)
    // Insert the coalesced block (if any) at the front of the free list
    // reference: #define NEXT_FREE(bp) (*(void **)(bp))
    // reference: #define PREV_FREE(bp) (*(void **)(bp + WSIZE))
    NEXT_FREE(bp) = free_listp;
    PREV_FREE(free_listp) = bp;
    PREV_FREE(bp) = NULL;
    free_listp = bp;

    // Return the coalesced block
    return bp;
}

static void *find_fit(size_t size) { // traverse the free list to find the size target (first fit esque)
    void *bp;

    // loop through the freelist_p until we find large enough free block
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREE(bp)) {
        if (size <= GET_SIZE(HDRP(bp)))
            return bp;
    }

    return NULL; // Otherwise no free block was large enough so return NULL
}

static void place(void *bp, size_t asize) { // similar to implicit mm.c but with freeblock() and coalesce()
    size_t fsize = GET_SIZE(HDRP(bp));      // size of current block, which is a free block

    // Case 1: Splitting is performed
    // size of current free block is big enough to fit more blocks after asize block
    if ((fsize - asize) >= (MINBLOCKSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1)); // make current block header&footer indicate new appended block
        PUT(FTRP(bp), PACK(asize, 1));
        remove_freeblock(bp);                  // remove bp from free block list
        bp = NEXT_BLKP(bp);                    // point to where the next block (the remaining free) should be
        PUT(HDRP(bp), PACK(fsize - asize, 0)); // update the new free block with due size
        PUT(FTRP(bp), PACK(fsize - asize, 0)); // update the footer accordingly as well
        coalesce(bp);                          // coalesce any adjacent blocks
    }
    // Case 2: Splitting not possible. Use the full free block
    // size of the current free block is not large enough to fit additional blocks (risk fragmentation)
    else {
        PUT(HDRP(bp), PACK(fsize, 1)); // update header&footer with new input block size
        PUT(FTRP(bp), PACK(fsize, 1));
        remove_freeblock(bp); // remove bp from free block list
    }
}

// (NEW to explicit allocator)
// removes the given free block from the free list (doubly linked list)
// reference: #define NEXT_FREE(bp) (*(void **)(bp))
// reference: #define PREV_FREE(bp) (*(void **)(bp + WSIZE))
static void remove_freeblock(void *bp) {
    if (bp) {                                         // if the input pointer is valid
        if (PREV_FREE(bp))                            // if prev_free pointer has value
            NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp); // make previous free block's next_free pointer point to the next_free of current block
        else                                          // if prev_free pointer is invalid
            free_listp = NEXT_FREE(bp);               // update the free_listp pointer to point to the next free block

        if (NEXT_FREE(bp) != NULL)                    // if the next_free pointer has value
            PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp); // make next free block's prev_free pointer point to the prev_free of current block
    }
}