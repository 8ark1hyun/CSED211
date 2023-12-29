/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * Implement a Dynamic Storage Allocator
 * Using Segregated free list and Best fit
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4             //Word and header/footer size (bytes)
#define DSIZE 8             //Double word size (bytes)
#define CHUNKSIZE (1 << 12) //Extend heap by this amount (bytes)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of next and previous segregated free list blocks */
/* Read the i-th segregated free list block */
#define NEXT_SEG_BLKP(bp) (*(char **)(bp + WSIZE))
#define PREV_SEG_BLKP(bp) (*(char **)(bp))
#define SEG_POINTER(i) (*((char **)seg_listp + i))


static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static int get_index(size_t size);
static void add_seg_list_block(void *bp, size_t size);
static void delete_seg_list_block(void *bp);

/* Heap Consistency Checker */
/*
int mm_check(void);
static int mark_or_not(void);
static int coalesce_or_not(void);
static int freeinlist_or_not(void);
static int overlap_or_not(void);
static int valid_or_not(void);
*/

static char* heap_listp;
static char* seg_listp;

/* 
 * mm_init - Initialize the malloc package
 */
int mm_init(void)
{
    int i;

    /* Create the initial segregated free list */
    if ((seg_listp = mem_sbrk(32 * WSIZE)) == (void *) -1) //Expand the heap
        return -1;
    for (i = 0; i < 32; i++)
        SEG_POINTER(i) = NULL;

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1) //Expand the heap
        return -1;
    PUT(heap_listp, 0);                                    //Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));         //Prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));         //Prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));             //Epilogue header
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL)                    //Extend the heap
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer
 *     Always allocate a block whose size is a multiple of the alignment
 */
void *mm_malloc(size_t size)
{
    size_t asize;      //Adjusted block size
    size_t extendsize; //Amount to extend heap if no fit
    char *bp;          //Block pointer

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs */
    asize = ALIGN(size + DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);                       //Place the block
        return bp;
    }

    /* No fit found */
    /* Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL) //Extend the heap
        return NULL;
    place(bp, asize);                           //Place the block
    return bp;
}

/*
 * mm_free - Free a block
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); //Block size

    PUT(HDRP(ptr), PACK(size, 0));     //Free block header
    PUT(FTRP(ptr), PACK(size, 0));     //Free block footer
    coalesce(ptr);                     //Coalesce the free blocks
}

/*
 * mm_realloc - Reallocate a block
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *old_ptr = ptr; //Old block pointer
    void *new_ptr = ptr; //New block pointer
    size_t asize;        //Block size
    size_t total_size;   //Total Block size

    /* If ptr is NULL, the call is equivalent to mm_malloc(size); */
    /* If size is equal to zero, the call is equivalent to mm_free(ptr); */
    if (old_ptr == NULL)
    {
        return mm_malloc(size);
    }
    else if (size == 0)
    {
        mm_free(old_ptr);
        return NULL;
    }

    /* If ptr is not NULL and size is not zero */
    /* Adjust block size to include overhead and alignment reqs */
    asize = ALIGN(size + DSIZE);

    if (GET_SIZE(HDRP(old_ptr)) >= asize) //Old block size >= New block size
    {
        return ptr;
    }
    else                                  //Old block size < New block size
    {
        total_size = GET_SIZE(HDRP(old_ptr)) + GET_SIZE(HDRP(NEXT_BLKP(old_ptr))); //Total block size
        
        if (!GET_ALLOC(HDRP(NEXT_BLKP(old_ptr))) && total_size >= size) //If Next of old block is not allocated and total size >= size
        {
            delete_seg_list_block(NEXT_BLKP(old_ptr)); //Delete the block from the segregated free list
            PUT(HDRP(old_ptr), PACK(total_size, 1));   //Pack a size and allocated bit into a word
            PUT(FTRP(old_ptr), PACK(total_size, 1));   //Pack a size and allocated bit into a word
        }
        else                                                            //Otherwise
        {
            new_ptr = mm_malloc(asize);                        //Allocate a new block
            memcpy(new_ptr, old_ptr, GET_SIZE(HDRP(old_ptr))); //Copy old block to new block
            mm_free(old_ptr);                                  //Free the old block
        }
        return new_ptr;
    }
}

/*
 * extend_heap - Extend the heap with a new free block
 */
static void *extend_heap(size_t words)
{
    char *bp;    //Block pointer
    size_t size; //Block size

    /* Adjust block size to include overhead and alignment reqs */
    size = ALIGN(words);

    if ((long)(bp = mem_sbrk(size)) == -1) //Expand the heap by size bytes
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));          //Free block header
    PUT(FTRP(bp), PACK(size, 0));          //Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  //New epilogue header

    /* Coalesce if the previous block was free */
    return coalesce(bp);                   //Coalesce the free blocks
}

/*
 * coalesce - Coalesce the free blocks
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //Allocated bit of previous block
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //Allocated bit of next block
    size_t size = GET_SIZE(HDRP(bp));                   //Block size

    if (prev_alloc && next_alloc)       //Case 1
    {
        add_seg_list_block(bp, size);                                           //Add a block into the segregated free list
        return bp;
    }
    else if (prev_alloc && !next_alloc) //Case 2
    {
        delete_seg_list_block(NEXT_BLKP(bp));                                   //Delete the next block From the segregated free list
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));                                  //Update the next block size
        PUT(HDRP(bp), PACK(size, 0));                                           //Free block header
        PUT(FTRP(bp), PACK(size, 0));                                           //Free block footer
    }
    else if (!prev_alloc && next_alloc) //Case 3
    {   
        delete_seg_list_block(PREV_BLKP(bp));                                   //Delete the previous block From the segregated free list
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));                                  //Update the previous block size
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                                //Free previous block header
        PUT(FTRP(bp), PACK(size, 0));                                           //Free block footer
        bp = PREV_BLKP(bp);                                                     //Previous block pointer
    }
    else                                //Case 4
    {
        delete_seg_list_block(PREV_BLKP(bp));                                   //Delete the previous block From the segregated free list
        delete_seg_list_block(NEXT_BLKP(bp));                                   //Delete the next block From the segregated free list
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  //Update the block size
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                                //Free previous block header
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                                //Free next block header
        bp = PREV_BLKP(bp);                                                     //Previous block pointer
    }
    add_seg_list_block(bp, size);                                               //Add a block into the segregated free list

    return bp;
}

/*
 * find_fit - Search the free list for a fit
 */
static void *find_fit(size_t asize)
{
    int i;
    int index = get_index(asize); //index of free list
    void *ptr;                    //temp pointer
    void *bp = NULL;              //Block pointer

    /* Search the free list for a fit */
    for (i = index; i < 32; i++)
    {
        for(ptr = SEG_POINTER(i); ptr != NULL; ptr = NEXT_SEG_BLKP(ptr))
            if(GET_SIZE(HDRP(ptr)) >= asize)
                if((bp == NULL) || (GET_SIZE(HDRP(ptr)) < GET_SIZE(HDRP(bp))))
                    bp = ptr;
        if(bp != NULL)
            return bp;
    }
    
    return NULL; //No fit
}

/*
 * place - Place the block
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); //Block size
    delete_seg_list_block(bp);         //Delete the block From the segregated free list

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));         //Pack a size and allocated bit into a word
        PUT(FTRP(bp), PACK(asize, 1));         //Pack a size and allocated bit into a word
        bp = NEXT_BLKP(bp);                    //Next block pointer
        PUT(HDRP(bp), PACK(csize - asize, 0)); //Free block header
        PUT(FTRP(bp), PACK(csize - asize, 0)); //Free block footer
        add_seg_list_block(bp, csize - asize); //Add a block into the segregated free list
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));         //Pack a size and allocated bit into a word
        PUT(FTRP(bp), PACK(csize, 1));         //Pack a size and allocated bit into a word
    }
}

/*
 * get_index - Get the index of the free list
 */
static int get_index(size_t size)
{
    int index; //index of free list

    /* Get the index of the free list */
    for (index = 0; index < 32; index++)
        if(size <= (1 << index))
            return index;
    return index;
}

/*
 * add_seg_list_block - Add a block into the segregated free list
 */
static void add_seg_list_block(void *bp, size_t size)
{
    int index = get_index(size); //index of free list

    /* Add a block into the segregated free list */
    PREV_SEG_BLKP(bp) = NULL;
    NEXT_SEG_BLKP(bp) = SEG_POINTER(index);
    if (SEG_POINTER(index) != NULL)
        PREV_SEG_BLKP(SEG_POINTER(index)) = bp;
    SEG_POINTER(index) = bp;
}

/*
 * delete_seg_list_block - Delete the block from the segregated free list
 */
static void delete_seg_list_block(void *bp)
{
    int size = GET_SIZE(HDRP(bp)); //Block size
    int index = get_index(size);   //index of free list

    /* Delete the block from the segregated free list */
    if (SEG_POINTER(index) != bp)
    {
        if (NEXT_SEG_BLKP(bp) != NULL)
            PREV_SEG_BLKP(NEXT_SEG_BLKP(bp)) = PREV_SEG_BLKP(bp);
        NEXT_SEG_BLKP(PREV_SEG_BLKP(bp)) = NEXT_SEG_BLKP(bp);
    }
    else
    {
        if (NEXT_SEG_BLKP(bp) != NULL)
            PREV_SEG_BLKP(NEXT_SEG_BLKP(bp)) = NULL;
        SEG_POINTER(index) = NEXT_SEG_BLKP(bp);
    }
}

/* Heap Consistency Checker */
/*
int mm_check(void)
{
    if (mark_or_not() == 0)
        return 0;
    if (coalesce_or_not() == 0)
        return 0;
    if (freeinlist_or_not() == 0)
        return 0;
    if (overlap_or_not() == 0)
        return 0;
    if (valid_or_not() == 0)
        return 0;

    return 1;
}
*/

/* Is every block in the free list marked as free? */
/*
static int mark_or_not(void)
{
    int i;
    void* ptr;
    
    for (i = 0; i < 32; i++)
    {
        for (ptr = SEG_POINTER(i); ptr != NULL; ptr = NEXT_SEG_BLKP(ptr))
        {
            if (GET_ALLOC(HDRP(ptr)) || GET_ALLOC(FTRP(ptr)))
            {
                printf("Error: Exist block in the free list marked as allocated\n");
                return 0;
            }
        }
    }
    return 1;
}
*/

/* Are there any contiguous free blocks that somehow escaped coalescing? */
/*
static int coalesce_or_not(void)
{
    char *ptr = heap_listp;

    for (ptr = NEXT_BLKP(ptr); GET_SIZE(ptr) != 0; ptr = NEXT_BLKP(ptr))
    {
        if ((GET_ALLOC(HDRP(ptr)) == 0) && (GET_ALLOC(HDRP(PREV_BLKP(ptr))) == 0))
        {
            printf("Error: Exist any contiguous free blocks that somehow escaped coalescing\n");
            return 0;
        }
    }
    return 1;
}
*/

/* Is every free block actually in the free list? */
/*
static int freeinlist_or_not(void)
{
    char *ptr;
    char *_ptr;
    int i;
    int flag;

    for (ptr = heap_listp; GET_SIZE(ptr) != 0; ptr = NEXT_BLKP(ptr))
    {
        if ((GET_ALLOC(HDRP(ptr)) == 0))
        {
            flag = 0;
            for (i = 0; i < 32; i++)
            {
                for (_ptr = SEG_POINTER(i); _ptr != NULL; _ptr = NEXT_SEG_BLKP(_ptr))
                {
                    if (ptr == _ptr)
                    {
                        flag = 1;
                        break;
                    }
                }
            }
            if (flag == 0)
            {
                printf("Error: Exist Free block that is not in free list");
            }
        }
    }
    return 1;
}
*/

/* Do any allocated blocks overlap? */
/*
static int overlap_or_not(void)
{
    char *ptr;

    for (ptr = heap_listp; GET_SIZE(ptr) != 0; ptr = NEXT_BLKP(ptr))
    {
        if ((GET_ALLOC(HDRP(ptr)) == 1))
        {
            if(ptr + GET_SIZE(HDRP(ptr)) - WSIZE >= NEXT_BLKP(ptr))
            {
                printf("Error: Exist allocated blocks overlapped\n");
                return 0;
            }
        }
    }
    return 1;
}
*/

/* Do the pointers in a heap block point to valid heap address? */
/*
static int valid_or_not(void)
{
    char *ptr;

    for(ptr = NEXT_BLKP(heap_listp); GET_SIZE(ptr) != 0; ptr = NEXT_BLKP(ptr))
    {
        if(HDRP(ptr) < HDRP(NEXT_BLKP(heap_listp)))
        {
            printf("Error: Exist not valid pointer\n");
            return 0;
        }
    }
    return 1;
}
*/