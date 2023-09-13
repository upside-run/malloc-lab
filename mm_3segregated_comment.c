/*
 ->  Malloc implementation using segregated fits with address-ordered explicit linked lists and reallocation heuristics
 ->  - Free blocks are stored in one of many linked lists segregated by block size.
 ->  - The n-th list contains blocks with a byte size that spans 2^n to 2^(n+1)-1.
 ->  - Within each list, blocks are sorted by memory address in ascending order.

/*****************************************************************************************
 ************************ DIRECTIVES, MACROS, INLINES, PROTOTYPES ************************
 *****************************************************************************************/

#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

//////// Team details ////////

team_t team = {"week5-team2", "kai", "kiyoungk_kim@hotmail.com", "", ""};

//////////////// Block size and alignment ////////////////

#define ALIGNMENT 8                                     // 8B Double word alignment standard
#define WSIZE 4                                         // 4B Word size, used for headers/footers
#define DSIZE 8                                         // 8B Double word size
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // Aligns size to nearest multiple of 8

//////////////// Memory management constants ////////////////

#define INITCHUNKSIZE (1 << 6)  // 64B Initial heap size
#define CHUNKSIZE (1 << 12)     // 4096B Default heap extension size
#define LISTLIMIT 20            // 20 Max segregated lists
#define REALLOC_BUFFER (1 << 7) // 128B Buffer for reallocations

//////////////// Header/footer manipulation functions and macros ////////////////

static inline size_t PACK(size_t size, int alloc) { return ((size) | (alloc & 0x1)); }
// Combines size and allocation flag (into a word, with alloc value into lower bit)
static inline size_t GET(void *p) { return *(size_t *)p; }
// Returns value at pointer p (read or write at address p)
static inline size_t GET_SIZE(void *p) { return GET(p) & ~0x7; } // & NOT 111 (not the last 3 digits)
// Returns size value from address p
static inline int GET_ALLOC(void *p) { return GET(p) & 0x1; }
// Returns allocation flag (0/1) from address p
static inline size_t GET_TAG(void *p) { return GET(p) & 0x2; } // Used to delay coalescing operations for performance
// Returns allocation tag from address p
#define PUT(p, val) (*(unsigned int *)(p) = (val) | GET_TAG(p))
// Sets value with current tag

static inline void PUT_NOTAG(void *p, size_t val) { *((size_t *)p) = val; }
// Sets value without modifying tag (clears relocation bit)
static inline size_t SET_RATAG(void *p) { return GET(p) | 0x2; }
// Sets allocation tag for value at p (adjusts allocation tag)
static inline size_t REMOVE_RATAG(void *p) { return GET(p) & 0x2; }
// Removes allocation tag from value at p (adjusts allocation tag)

//////////////// Block navigation functions and macros ////////////////

static inline void *HDRP(void *bp) { return ((char *)bp) - WSIZE; }
// Returns header of block
static inline void *FTRP(void *bp) { return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE); }
// Returns footer of block
static inline void *NEXT_BLKP(void *ptr) { return ((char *)(ptr) + GET_SIZE(((char *)(ptr)-WSIZE))); }
// Navigates to next block's payload
static inline void *PREV_BLKP(void *ptr) { return ((char *)(ptr)-GET_SIZE(((char *)(ptr)-DSIZE))); }
// Navigates to previous block's payload

//////////////// Linked list pointer helper functions and macros ////////////////

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))
// Store predecessor or successor pointer for free blocks
static inline void *PRED_PTR(void *ptr) { return ((char *)(ptr)); }
// Returns predecessor pointer (address of free block's predecessor entry)
static inline void *SUCC_PTR(void *ptr) { return ((char *)(ptr) + WSIZE); }
// Returns successor pointer (address of free block's successor entry)
static inline void *PRED(void *ptr) { return (*(char **)(ptr)); }
// Dereferences segregated list and returns predecessor address
static inline void *SUCC(void *ptr) { return (*(char **)(SUCC_PTR(ptr))); }
// Dereferences segregated list and returns successor address

//////////////// Array to manage free blocks in segregated lists ////////////////
void *segregated_free_lists[LISTLIMIT];

//////////////// Utility functions ////////////////
static inline int MAX(int x, int y) { return x > y ? x : y; } // Returns the max of two values
static inline int MIN(int x, int y) { return x < y ? x : y; } // Returns the min of two values

//////////////// Internal helper function prototypes ////////////////
static void *extend_heap(size_t size);           // Extends the heap by the specified size
static void *coalesce(void *ptr);                // Coalesces adjacent free blocks
static void *place(void *ptr, size_t asize);     // Allocates block with adjustments
static void insert_node(void *ptr, size_t size); // Inserts block into free list
static void delete_node(void *ptr);              // Deletes block from free list

/******************************************************************
 ************************ HELPER FUNCTIONS ************************
 ******************************************************************/

/* extend_heap - Expands the heap with a new free block.
 * - @parameter : SIZE (number of bytes by which to expand the heap)
 * - @return : POINTER to beginning of this new free block
 * - (1) Extended space is added to free blocks list
 * - (2) Headers & footers contain info on size & allocation */
static void *extend_heap(size_t size) {
    void *ptr;    // Pointer to the new block.
    size_t asize; // Adjusted block size for alignment.

    // Align the requested size to meet our memory alignment requirements.
    asize = ALIGN(size);

    // Request additional space from the system to expand the heap.
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL; // If there's an error in expanding, return NULL.

    // Initialize the block's header and footer.
    // The block is marked as free (0 in the PACK macro).
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0)); // Set header for the new block.
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0)); // Set footer for the new block.

    // Set the next block's header to indicate the end of the heap space.
    // It's marked as allocated (1 in the PACK macro) to avoid merging with future extended blocks.
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));

    // Add the new block to our free list (or relevant data structure).
    insert_node(ptr, asize);

    // Adjust the position and size of the new block in case it's adjacent to another free block.
    // This process merges adjacent free blocks to form a larger continuous free space.
    return coalesce(ptr);
}

/* insert_node - Inserts a free block into the segregated free list.
 * - @parameter : POINTER to the block that we are inserting.
 * - @parameter : SIZE of the block we are inserting.
 * - @return : NOTHING.
 * (1) First traverses the array of segregated lists to find the right index.
 * (2) Inserts free block to appropriate segregated list based on size (Descending Order). */
static void insert_node(void *ptr, size_t size) {
    int list = 0;            // Initiate index to select the appropriate list.
    void *search_ptr = ptr;  // Pointer used to traverse the segregated list.
    void *insert_ptr = NULL; // Pointer to the block after which new block is inserted.

    // Determine the appropriate list for the given block size.
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1; // size is right-shifted by one, meaning divided by two.
        list++;     // list index is increased by one; 2^list = max of each list.
    }               // Appropriate size and list values are decided here.

    // Begin search from the start of the determined list.
    search_ptr = segregated_free_lists[list];

    // Traverse the list to find the correct position for the block.
    // To maintain address order, we traverse the list from larger address to smaller address.
    // This allows higher chances of finding cached blocks and allows better memory utilization.
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    } // Appropriate position within the list index is decided here
      // NOTE : if there is just one entry and its bigger than what we're inserting, search_ptr == NULL && insert_ptr != NULL.

    // Insert the block based on the position of other blocks in the list.
    if (search_ptr != NULL) {                   // (1) If there is a valid entry in this list index.
        if (insert_ptr != NULL) {               // (1-1) If there is a valid position where we can push new node into.
            SET_PTR(SUCC_PTR(search_ptr), ptr); // -> Insert in the middle of the list (in place of insert_ptr).
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {                                // (1-2) If there is NO insert_ptr to push into (meaning that this is the largest in this index list).
            SET_PTR(PRED_PTR(ptr), search_ptr); // -> Insert at the beginning of the list.
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr; // -> And dont for get to update the index list's start pointer.
        }
    } else {                              // (2) If there is NO valid entry in this list index (search_ptr == NULL).
        if (insert_ptr != NULL) {         // (2-1) Check "NOTE" above: there is just one node in this list that is bigger than what we're inserting.
            SET_PTR(PRED_PTR(ptr), NULL); // -> Insert at the end of the list.
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {                          // (2-2) List is empty (both search & insert ptrs are NULL).
            SET_PTR(PRED_PTR(ptr), NULL); // -> Insert as the first block in this list.
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr; // -> Update the list's start pointer; latest freed block is at the beginning of the list (chances of cache).
        }
    }
    return; // Just exit the function, no need to return anything.
}

/* delete_node - Removes a block from the segregated free list.
 * - @parameter : POINTER to the block we are removing.
 * - @return : NOTHING.
 * (1) Determines which segregated list the block belongs to.
 * (2) Removes the block from that list, usually after a free block has been allocated or coalesced.
 * (3) Effectively unlink from the list, update neighbours' pointers. */
static void delete_node(void *ptr) {
    int list = 0; // Initialize index to select the appropriate list.
    size_t size = GET_SIZE(HDRP(ptr));

    // Determine which list the block belongs to based on its size.
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1; // Effectively divides size by two (same logic from insert_node).
        list++;
    } // Appropriate size and list values are decided here.

    // Handle block removal based on its position in the list.
    if (PRED(ptr) != NULL) {                         // (1) If the block has a predecessor.
        if (SUCC(ptr) != NULL) {                     // (1-1) If the block also has a successor -> block is in the middle of the list.
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr)); // -> Set predecessor's succ_ptr to current block's successor.
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr)); // -> Set successor's pred_ptr to current block;s predecessor.
        } else {                                     // (1-2) If the block doesn't have a successor -> block is at the end of the list.
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);      // -> Change predecessor's succ_ptr to NULL.
            segregated_free_lists[list] = PRED(ptr); // -> make the pointer point to the earlier address in the list (address-order).
        }
    } else {                                    // (2) If the block does NOT have a predecessor.
        if (SUCC(ptr) != NULL) {                // (2-1) If it has a successor -> block is at the beginning of the list.
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL); // -> Set successor's pred_ptr to NULL.
        } else {                                // (2-2) If it does NOT have a succesor -> block is the only one in the list.
            segregated_free_lists[list] = NULL; // -> Set the list pointer to NULL.
        }
    }
    return;
}

/* coalesce - Combines adjacent free blocks in memory to form a larger free block.
 * - @parameter : POINTER to the block we want to start coalescing.
 * - @return : POINTER to coalesced block.
 * (1) Checks the typical 4-scenario cases to coalesce blocks and save to free lists. */
static void *coalesce(void *ptr) {
    // Check if the previous and next blocks are allocated or not.
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    // If the previous block has a "remove allocation" tag, consider it as allocated.
    // Realloc function sets these RA tags to the subsequent block when the block it resizes is close to fully utilized.
    // By doing so, in case of frequent/subsequent realloc calls to that block (again), it can make use of this 'next block'
    if (GET_TAG(HDRP(PREV_BLKP(ptr))))
        prev_alloc = 1;

    // Four possible scenarios based on the allocation status of adjacent blocks:

    // 1. Both previous and next blocks are allocated (1, 1). Nothing to merge.
    if (prev_alloc && next_alloc) {
        return ptr;
    }

    // 2. Previous block is allocated, but the next block is free (1, 0). Merge with the next block.
    else if (prev_alloc && !next_alloc) {
        delete_node(ptr);                       // Remove the current block from the free list.
        delete_node(NEXT_BLKP(ptr));            // Remove the next block from the free list.
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr))); // Update size to the combined size.
        PUT(HDRP(ptr), PACK(size, 0));          // Update the header of the current block.
        PUT(FTRP(ptr), PACK(size, 0));          // Update the footer of the current block.
    }

    // 3. Next block is allocated, but the previous block is free (0, 1). Merge with the previous block.
    else if (!prev_alloc && next_alloc) {
        delete_node(ptr);                         // Remove the current block from the free list.
        delete_node(PREV_BLKP(ptr));              // Remove the previous block from the free list.
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));   // Update size to the combined size.
        PUT(FTRP(ptr), PACK(size, 0));            // Update the footer of the current block.
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0)); // Update the header of the previous block.
        ptr = PREV_BLKP(ptr);                     // Point to the beginning of the coalesced block.
    }

    // 4. Both previous and next blocks are free (0, 0). Merge all three blocks.
    else {
        delete_node(ptr);                                                        // Remove the current block from the free list.
        delete_node(PREV_BLKP(ptr));                                             // Remove the previous block from the free list.
        delete_node(NEXT_BLKP(ptr));                                             // Remove the next block from the free list.
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr))); // Update size to the combined size of all three blocks.
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));                                // Update the header of the previous block.
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));                                // Update the footer of the next block.
        ptr = PREV_BLKP(ptr);                                                    // Point to the beginning of the coalesced block.
    }

    // After coalescing, insert the new, larger block into the free list.
    insert_node(ptr, size);

    return ptr; // Return the pointer to the coalesced block.
}

/* place - Allocates a block of size `asize` from a free block pointed by `ptr`.
 * - @parameter : POINTER to the free block where we 'place' the new block.
 * - @parameter : SIZE to be allocated (size of new block).
 * - @return : POINTER to the newly allocated block.
 * (1) Split the free block if remainder after allocation is large enough.
 * (2) Special condition if requested size is large (100+) -> You can test this by masking it out. */
static void *place(void *ptr, size_t asize) {

    size_t ptr_size = GET_SIZE(HDRP(ptr)); // Get the total size of the free block.
    size_t remainder = ptr_size - asize;   // Calculate how much space will be left after allocating `asize`.
    delete_node(ptr);                      // Remove the block from the free list since it's being allocated.

    // If the remaining space isn't enough to form another free block after splitting, don't split.
    if (remainder <= DSIZE * 2) {
        PUT(HDRP(ptr), PACK(ptr_size, 1)); // Mark the entire block as allocated.
        PUT(FTRP(ptr), PACK(ptr_size, 1)); // Update the footer too.
    }
    // If the requested size is large (>= 100) and splitting results in a usable free block.
    // NOTE: Allocating from the tail (beneficial if larger sizes are likely to be freed soon; better coalescing)
    // NOTE: May result in worse performance if application doesn't exhibit this behaviour (TRY MASKING THIS SECTION)
    else if (asize >= 100) {
        PUT(HDRP(ptr), PACK(remainder, 0)); // Allocate the tail part of the block.
        PUT(FTRP(ptr), PACK(remainder, 0));
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1)); // Allocate space for the new block header.
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1)); // And the new block footer.

        insert_node(ptr, remainder); // Insert the remainder part back into the free list.
        return NEXT_BLKP(ptr);       // Return pointer to the next block since we allocated from the tail part.
    }
    // The general case where the block is split into an allocated block and a smaller free block.
    else {
        PUT(HDRP(ptr), PACK(asize, 1));                      // Allocate the required space.
        PUT(FTRP(ptr), PACK(asize, 1));                      // Update the footer.
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); // Mark the remainder as free.
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0));

        insert_node(NEXT_BLKP(ptr), remainder); // Insert the remainder back into the free list.
    }

    return ptr; // Return the pointer to the allocated block.
}

/****************************************************************
 ************************ MAIN FUNCTIONS ************************
 ****************************************************************/

/* mm_init - Initializes the memory manager.
 * - @paramter : VOID
 * - @return : 0 if successful, or -2 if there's an error
 * (1) Sets up the initial empty heap with a prologue & epilogue blocks
 * (2) Also initializes the segregated free lists array */
int mm_init(void) {
    int list;         // Local variable for loop iteration.
    char *heap_start; // Pointer to the start of the heap.

    // Initialize all entries in the segregated free lists to NULL.
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }

    // Expand the heap by 16B (preparation)
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1; // If unable to expand the heap, return error.

    // Initialization of the prologue and epilogue blocks.
    PUT_NOTAG(heap_start, 0);                            // Padding.
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); // Prologue header.
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); // Prologue footer.
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     // Epilogue header.

    // Extend the heap by a default initial size.
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1; // If unable to extend the heap, return error.

    return 0; // Successfully initialized.
}

/* mm_malloc - Allocates a block of memory of the specified size.
 * - @parameter : SIZE of the memory to allocate
 * - @return : POINTER to allocated block
 * (1) First adjust the request size to include overhead and alignment requirements
 * (2) Search the appropriate list for a free block that fits the size
 * (3) If none found, extend the heap */
void *mm_malloc(size_t size) {
    size_t asize;      // Adjusted block size.
    size_t extendsize; // Amount to extend heap if no fit.
    void *ptr = NULL;  // Block pointer.
    int list = 0;      // List index.

    // Ignore request if size == 0.
    if (size == 0)
        return NULL;

    // Adjust block size to include overhead and alignment requirements.
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size + DSIZE);
    }

    // Start searching from the appropriate list.
    size_t searchsize = asize;
    while (list < LISTLIMIT) {

        // (1) If the list is the last list (wildcard list),
        // OR (2) If the list may have blocks of desired size (meets size requirement AND is not NULL)
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            ptr = segregated_free_lists[list];

            // Traverse through the free list to find a suitable block.
            //// While (list has not ended AND the target size is bigger)
            //// OR (if the block is RA tagged), continue traversing.
            // The RA tag essentially tells the loop to pass on the block if it is tagged.
            // This makes sure that the block before RA tag can use the tagged block in future realloc calls.
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))) || (GET_TAG(HDRP(ptr))))) {
                ptr = PRED(ptr);
            } // NOTE: This allocator is segregated fits with address-ordered explicit linked lists.
              // NOTE: The segregated array itself is in descending order (large size first),
              //// then the addresses in individual lists are linked such that lower addresses come first (maintaining order).
              // By using PRED(), we are traversing toward the beginning of the list toward lower addresses.
              // This allows better memory utilization, plus better chance of finding something in cache.

            // If a block is found, exit loop.
            if (ptr != NULL)
                break;
        }

        // Move to the next list.
        searchsize >>= 1;
        list++;
    }

    // If no block is found, extend the heap.
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }

    // Place the block.
    ptr = place(ptr, asize);
    return ptr;
}

/* mm_free - Frees a block of memory previously allocated by mm_malloc.
 * - @parameter : POINTER to the block of memory that we want to free.
 * - @return : NOTHING.
 * (1) Marks the block as free (change allocation status).
 * (2) Tries to coalesce if possible. */
void mm_free(void *ptr) {

    size_t size = GET_SIZE(HDRP(ptr)); // Get the size of the block to be freed.

    REMOVE_RATAG(HDRP(NEXT_BLKP(ptr))); // Remove reallocation tag from the next block (check realloc)

    PUT(HDRP(ptr), PACK(size, 0)); // Mark the block as free by updating its header and footer.
    PUT(FTRP(ptr), PACK(size, 0));

    insert_node(ptr, size); // Insert the free block into the segregated free list.

    coalesce(ptr); // Attempt to merge this block with adjacent free blocks.

    return;
}

/* mm_realloc - Resizes the block of memory pointed by ptr to the size bytes.
 * - @parameter : POINTER to the block we want to resize.
 * - @parameter : SIZE that we want to change it to.
 * - @return : POINTER to the resized block
 * (1) Adjusts the size of the memory block.
 * (2) If it can be extended in place (coalesced), do it.
 * (3) If not, allocate a new block, copy the content and free the old one. */
void *mm_realloc(void *ptr, size_t size) {
    void *new_ptr = ptr;    // Initialize new_ptr as pointer to block we want to resize
    size_t new_size = size; // Initizalize new_size to do the same
    int remainder, extendsize, balancer;

    // If the new size is 0, return NULL.
    if (size == 0)
        return NULL;

    // Adjust the size to include the overhead and alignment reqs.
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size + DSIZE);
    }

    // Optimization technique for realloc; create a buffer for future realloc calls (save on traversal costs).
    new_size += REALLOC_BUFFER;

    // Calculate how much we need to expand or contract.
    balancer = GET_SIZE(HDRP(ptr)) - new_size;

    // If the block needs to be expanded (if there is no surplus).
    if (balancer < 0) {

        // (1) If the next block is free or if the next block is an epilogue block.
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {

            // Calculate how much memory we are still short of.
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;

            // If we are still short on space after coalsescing, extend heap.
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL) // extend_heap creates a new epilogue block later.
                    return NULL;
                remainder += extendsize; // Now the new remainder should be able to host the target size.
            }

            // Coalesce and set the block size (header and footer).
            delete_node(NEXT_BLKP(ptr));
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1));
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1));
        }

        // (2) If the next block is not free.
        else {
            // Allocate a new block, copy the content and free the old block.
            new_ptr = mm_malloc(new_size - DSIZE); // Use the  new new_ptr pointer and leave ptr alone.
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }

        balancer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }

    // Set a reallocation tag for the next block if the block size is within a certain range.
    // This effectively anticipates the behavior of applications that might make frequent realloc calls.
    // THe next block is RA tagged if surplus space of current block is is relatively small,
    //// so combined with the code in coalesce(), we are telling the coalesce function to not touch that block,
    //// and combined with the code in malloc(), we are telling the malloc function to not touch that block.
    // In case of future realloc calls to this block, the realloc function can utilize the block that is RA-tagged.
    if (balancer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));

    return new_ptr;
}
