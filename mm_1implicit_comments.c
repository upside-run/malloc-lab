/*********************************************************
 * Implicit free list + next fit
 * Perf index = 42 (util) + 40 (thru) = 82/100
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

#define WSIZE 4             // 4B Word Size
#define DSIZE 8             // 8B Double Word Size (Block Size 16B)
#define CHUNKSIZE (1 << 12) // 4096B (4MB) for initial free block and expanding heap

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // ternary operator to extract max value

#define PACK(size, alloc) ((size) | (alloc))       // pack size and allocator into one for header & footer
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // changes value of header & footer to 'val'
#define GET(p) (*(unsigned int *)(p))              // helper: reads content of the header & footer
#define GET_SIZE(p) (GET(p) & ~0x7)                // get size attributes in header & footer
#define GET_ALLOC(p) (GET(p) & 0x1)                // get allocator attributes in header & footer

#define HDRP(bp) ((char *)(bp)-WSIZE)                                 // returns pointer to current header
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)          // returns pointer to current footer
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // returns pointer to next block payload
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // returns pointer to previous block payload

void *next_fit_position;
// global pointer to the region returned from most recent malloc or free call
// initialized with mm_init, updated with coalesce (->mm_free, extend_heap), looped and updated with find_next

static char *heap_listp; // pointer to prologue block payload (= prologue block footer)
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*********************************************************
 * Core Functions of Malloc
 ********************************************************/

// initialize the function
int mm_init(void) {

    // create initial empty heap
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // if mem_sbrk fails (returns -1)
        return -1;
    PUT(heap_listp, 0);                            // alignment padding (very first block in heap)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header; 8B + allocated (1)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer; 8B + allocated (1)
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // epilogue footer; 0B + allocated (1)
    heap_listp += (2 * WSIZE);                     // move heap_listp pointer into position (payload of prologue)
    next_fit_position = heap_listp;                // initialize the global malloc call to the start of the heap for next_fit

    // extend empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // extend_heap takes in word sizes
        return -1;
    return 0;
}

// Allocate a block by incrementing the brk pointer
// Always allocate a block whose size is a multiple of the alignment
void *mm_malloc(size_t size) {
    size_t asize;      // adjusted block size
    size_t extendsize; // amount to extend heap if fit fails
    char *bp;          // declare bp

    if (size == 0) // ignore weird requests (like size of 0)
        return NULL;

    // Adjust block size to include overhead and alignment reqs.
    if (size <= DSIZE) // enforce minimum block size of 16B
        asize = 2 * DSIZE;
    else // if larger than 8 bytes, add overhead for header/footer (8B) then round up to nearest multiple of 8
        // rounding is done with first adding (DSIZE-1) to prepare for division, then dividing the sum by DSIZE
        // if size is already a multiple of DSIZE, the addition makes sure that we dont decrese the size of chunks
        // if size is not a multiple, the addition pushes the sum over the next multiple of DSIZE
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // Search the free list for a fit
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // With no fit found, get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

// free the target block
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp)); // get the size of current block
    PUT(HDRP(bp), PACK(size, 0));     // change header to unallocated (0)
    PUT(FTRP(bp), PACK(size, 0));     // change footer to unallocated (0)
    coalesce(bp);                     // now coalsece with adjacent free blocks
}

// Implemented simply in terms of mm_malloc and mm_free
void *mm_realloc(void *ptr, size_t size) { // ptr for block to resize, and size for new size
    void *oldptr = ptr;                    // save pointer to current block's payload as "OLD"
    void *newptr;                          // declare new pointer that will hold new size
    size_t copySize;

    newptr = mm_malloc(size); // assign VM to newptr
    if (newptr == NULL)       // if assigning fails, return NULL
        return NULL;

    copySize = GET_SIZE(HDRP(oldptr)); // else, get size of current pointer we want to resize
    if (size < copySize)               // if previous size is larger than new size,
        copySize = size;               // change copySize to the smaller value to avoid mem access errors (copying more than we should)
    memcpy(newptr, oldptr, copySize);  // destination, source, size -> copy data
    mm_free(oldptr);                   // free the old pointer to reclaim memory
    return newptr;                     // return pointer to newly sized block
}

/*********************************************************
 * Helper functions to support mm_malloc, mm_free, and mm_realloc
 ********************************************************/

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // if true (1), make even

    // if mem_sbrk fails (-1), return NULL
    if ((long)(bp = mem_sbrk(size)) == -1) // bp points to unallocated VM position
        return NULL;

    // initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));         // temporarily move bp one WSIZE to enter epilogue header, update new size
    PUT(FTRP(bp), PACK(size, 0));         // now temporarily move bp to new footer position and update the new size
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // lastly temporarily move bp to where epilogue should be and create it

    // Coalesce if the previous block was free
    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // get footer allocater attribute of previous block
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // get header allocator attribute of next block
    size_t size = GET_SIZE(HDRP(bp));                   // get size of current block

    // Case 1: both prev and next blocks are allocated (1, 1)
    if (prev_alloc && next_alloc) {
        next_fit_position = bp;
        return bp; // no need to coalesce
    }
    // Case 2: prev is allocated and next is free (1, 0)
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // increase 'size' by that of next block
        PUT(HDRP(bp), PACK(size, 0));          // make header of current block indicate new size
        PUT(FTRP(bp), PACK(size, 0));          // make footer of current block indicate new size; FTRP moves pointer by the new 'size'
    }
    // Case 3: prev is free and next is allocated (0, 1)
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // increase 'size' by that of prev block
        PUT(FTRP(bp), PACK(size, 0));            // make footer of current block indicate new size
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // make header of prev block indicate new size
        bp = PREV_BLKP(bp);                      // move bp to point at the payload of free block
    }
    // Case 4: both prev and next blocks are free (0, 0)
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // self explanatory
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    next_fit_position = bp;
    return bp;
}

static void *find_fit(size_t asize) {
    // Next-fit search
    void *bp;
    // loop through the heap starting from the next_fit_position
    for (bp = next_fit_position; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        // check if each block is free and if the size is big enough
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            next_fit_position = bp; // update the global variable
            return bp;
        }
    }
    next_fit_position = heap_listp; // if fit not found, reset pointer to the prologue and return NULL
    return NULL;
}

static void place(void *bp, size_t asize) { // place requested block at the beginning of free block
    size_t csize = GET_SIZE(HDRP(bp));      // size of current block, which is a free block

    // if size of current free block is big enough to fit more after asize block, SPLIT
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));         // make current block header indicate new appended block
        PUT(FTRP(bp), PACK(asize, 1));         // move to footer of that size to change footer attribute
        bp = NEXT_BLKP(bp);                    // now move the pointer to where the next block (the remaining free) should be
        PUT(HDRP(bp), PACK(csize - asize, 0)); // update the new free block with due size
        PUT(FTRP(bp), PACK(csize - asize, 0)); // update the footer accordingly as well
    }
    // if size of the remainder (c-a) is not equal or bigger than minimum block size of 16B
    else {
        PUT(HDRP(bp), PACK(csize, 1)); // update header with new input block size
        PUT(FTRP(bp), PACK(csize, 1)); // update footer as well
    }
}