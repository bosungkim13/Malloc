/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP3e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Team",
	/* First member's full name */
	"Renzo Espinoza",
	/* First member's NetID */
	"rme5",
	/* Second member's full name (leave blank if none) */
	"Bo Sung Kim",
	/* Second member's NetID (leave blank if none) */
	"bk39"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */
#define ALIGN (16)
#define NUM (16)

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  
#define BIN(x) __builtin_clz(x)


/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  
struct Node *free_lists;


/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insertBlock(void *bp);
static void deleteBlock(void *bp);
static int find_explicit(size_t size);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 


struct Node{
	struct Node* next;
	struct Node* prev;
};



/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{
	char* temp;
	if ((temp = mem_sbrk(NUM * DSIZE)) == (void*)-1){
		return (-1);
	}
	free_lists = (struct Node*)temp;
	for (unsigned int i = 0; i < NUM; i++){
		struct Node* cur = free_lists + i;
		cur->next = cur;
		cur->prev = cur;
	}

	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // changed mem_sbrk to match new inital heap
		return (-1);

	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */

	heap_listp += (2 * WSIZE);
	
	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = (ALIGN * ((size + (ALIGN - 1)) / ALIGN)) + DSIZE;

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = asize + (2 * WSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;
	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	bp = coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	
	size_t oldsize;
	void *newptr;
	size_t asize;
	oldsize = GET_SIZE(HDRP(ptr));

	if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	if (asize <= oldsize)
		return (ptr);

	/* If the next block is free, we allocate it*/
	size_t next_size = GET_SIZE(NEXT_BLKP(ptr));
	if ((!GET_ALLOC(NEXT_BLKP(ptr))) && ((oldsize + next_size) <= asize)){
		void* next = NEXT_BLKP(ptr);
		deleteBlock(next);
		/*Allocate block to account for new size */
		PUT(HDRP(ptr), PACK(oldsize + next_size, 1));
		PUT(FTRP(ptr), PACK(oldsize + next_size, 1));
		return (ptr);
	}

	//Get a new bit of free memory when realloc isn't possible on current heap
	newptr = mm_malloc(MAX(oldsize, asize) * 10);

	if (newptr == NULL){
		return (NULL);
	}

	//copy data
	memcpy(newptr, ptr, oldsize);

	mm_free(ptr);
	return (newptr);
}


/*
 * Helper function
 */

/*
 * Requires: 
 * "size" is the size of the block being entered into the free list
 * 
 * Effects:
 * 	Returns the number of the free_lists that it needs to be entered into  
 */
static int
find_explicit(size_t size)
{
	if (size <= 64){
		return (0);
	}
	else if (size <= 128){
		return (1);
	}
	else if (size <= 256){
		return (2);
	}
	else if (size <= 500){
		return (3);
	}
	else if (size <= 750) {
        return (4);
    }
    else if (size <= 1000) {
        return (5);
    }
    else if (size <= 2000) {
        return (6);
    }
	else if (size <= 3000) {
        return (7);
    }
    else if (size <= 4000) {
        return (8);
    }
    else if (size <= 5000) {
        return (9);
    }
    else if (size <= 6000) {
        return (10);
    }
    else if (size <= 7000) {
        return (11);
    }
    else if (size <= 8000) {
        return (12);
    }
    else if (size <= 9000) {
        return (13);
    }
    else {
        return (14);
    }


}


/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if (prev_alloc && next_alloc) {
		//if the previous block and next block
		//are both allocated then just insert there
		insertBlock((struct Node*)bp);                 			/* Case 1 */
		return (bp);
	} else if (prev_alloc && !next_alloc) {
		//if the next block is free and the
		//the prev block is allocated then coallese
		//the current block with the previous block /* Case 2 */
		//delete the next block in order to create
		//a new block of biggger size with the next block
		//and the current block
		deleteBlock((struct Node*)NEXT_BLKP(bp));
		//we increase the size of the block we are packing
		//and then put that
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		insertBlock((struct Node*)bp);
	} else if (!prev_alloc && next_alloc) { 
		//if the prev block is free and the next
		//block is allocated then delete the prev
		//block        								/* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		deleteBlock((struct Node*)PREV_BLKP(bp));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		insertBlock((struct Node*)bp);
	} else {                       
		//if the prev and next blocks are both
		//free we combine all three blocks           /* Case 4 */
		deleteBlock((struct Node*)NEXT_BLKP(bp));
		deleteBlock((struct Node*)PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		insertBlock((struct Node*)bp);
	}
	//checkheap(false);
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	size_t size;
	void *bp;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	struct Node *bp, *temp;
    int size = find_explicit(asize);
    /* find bin helps us find the best free list to start w */
    for (int i = size; i < NUM; i++) {
		//iterate through free list
        temp = free_lists + i;
        /* once we find a fit, that will be the best fit since seggregated lists are sorted*/
        for (bp = temp->next; bp != temp; bp = bp->next) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                return (bp);
            }
        }
    }
    return (NULL);
}


/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	//gets the size of the header of the block pointer
	size_t csize = GET_SIZE(HDRP(bp));   
	// if the block requires splitting
	if ((csize - asize) >= (ALIGN + DSIZE)) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		deleteBlock(bp);
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		struct Node* split = (struct Node *) bp;
		insertBlock(split);
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		struct Node* cur = (struct Node*) bp;
		deleteBlock(cur);
	}

	//checkheap(false);
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp))){
		printf("Bad epilogue header\n");
	}

	
	for (unsigned int i = 0; i < NUM; i++){
		struct Node* free_block = free_lists + i;
		free_block = free_block->next;
	
		if (free_block != NULL){
			while (free_block != free_lists + i) {
				/* Check if every block in the free list 
					* is a valid block.
					*/
				checkblock(free_block);
					
				// check if every node in the free list is free
				if (GET_ALLOC(HDRP(free_block))) {
					printf("Block in free list is allocated\n");

				} else {
					/* Check if there are any contiguous free block 
					* that somehow escaped coalescing.
					*/
					if ((char *) GET(bp + WSIZE) != NULL && 
					(void *) GET(bp + WSIZE) == 
					NEXT_BLKP(free_block)) 
						printf("Contiguous free blocks\n");
				}
				// iterate through the free list
				free_block = free_block->next;
			
			}
		}
	}
		
}



/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	size_t hsize, fsize;
	bool halloc, falloc;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * Requires:
 *   A pointer bp
 *
 * Effects:
 *   Deletes bp from the free list
 */
static void
deleteBlock(void *bp){
	struct Node *copy_bp = (struct Node *)bp;
	copy_bp->prev->next = copy_bp->next;
	copy_bp->next->prev = copy_bp->prev;
}

/*
 * Requires:
 *   A pointer bp
 *
 * Effects:
 *   Inserts bp into the free list
 */
static void
insertBlock(void *bp){
	
	struct Node *cur, *head, *temp;

	cur = (struct Node*)bp;

	//Find the explicit list
	int explicit = find_explicit(GET_SIZE(HDRP(bp)));
	//The explicit free list ptr
	head = free_lists + explicit;
	// The next free block in the explicit free list
	temp = head->next;
	
	// Add it to the head of the seggregated list
	head->next = cur;
	temp->prev = cur;
	cur->prev = head;
	cur->next = temp;
	
}