/*
 * mm.c - implementing malloc using an implicit free list.
 * 
 * The start of the heap is mantained via a global variable heap_listp, which points to the first block 
 * of the heap just past an unused block and a header/footer. The end of the heap is a single empty block of word size.
 * Each block within the heap has a header and footer of size word and then a double word aligned payload. Blocks can be
 * reallocated using realloc, which only uses malloc and free in a case where we need to find a new block. All free blocks
 * are coalesced. We find new blocks using a next_fit implementation, which mantains a global variable to the most recent
 * malloc call.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    "jwyattm",
    "Jacob Morris",
    "jwyattm@bu.edu",
    "",
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4 /* word size (bytes) */
#define DSIZE 8 /* doubleword size (bytes) */
#define CHUNKSIZE (1<<12) /* initial heap size (bytes) */
#define OVERHEAD 8 /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p)    (*(size_t *)(p))
#define PUT(p,val) (*(size_t *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *) (bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *heap_listp; /* global pointer to the start of the heap*/
void *last_malloc_call; /* global pointer to the region returned from most recent malloc or free call*/

static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static int mm_check(void);
static void *best_fit(size_t asize);
static void *next_fit(size_t asize);

// my mm test main for easier testing purposes
#ifdef MY_MMTEST
int main(int argc, char **argv)
{
  mem_init();
  mm_init();
  void * p;
  void * r;
  void *q;
  void *s;
  printf("%d/n", mm_check());

  p = mm_malloc(16);
  q = mm_malloc(8);
  
  mm_free(p);
  s = mm_malloc(8);
 
  r = mm_realloc(q,16);
  printf("%d/n", mm_check());

  /*printf("mm_check = %d", mm_check());*/
  /*void *r = mm_realloc(p,5);*/
  
    /*
  p = mm_malloc(1);
  printf("mm_malloc=%p\n", mm_malloc(1));
  r = mm_realloc(p,1);
  */
  return 0;

}
#endif

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL) { 
        return -1;
    }
    
    PUT(heap_listp, 0); /* create a 0 block at the start of the heap*/
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1)); /* create a header at the start of the heap*/
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1)); /* create the footer at the start of the heap*/
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1)); /* create the single block representing the end of the heap*/
    heap_listp += DSIZE; /* move the pointer to the start of the heap past the initial header/footer */
    last_malloc_call = heap_listp; /* initialize the global malloc call to the start of the heap for next_fit*/
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) { /* extend the heap to the maximum wanted size*/
        return -1; 
    }
    return 0;
}
    

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((int)(bp = mem_sbrk(size)) == -1){ /* check if mem_sbrk fails */
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

 /*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */


void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize; 
    char *bp;

    /* check if size is not positive*/
    if (size <= 0) {
        return NULL;
    }

    /* get the nearest alignment multiple of the size*/
    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;       
    }
    
    else {
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    }

    /* call the search function and allocate the found location*/
    if ((bp = next_fit(asize)) != NULL) {
        place(bp, asize);
    
    /* return a pointer to the allocated region*/
    return bp; 
    }

    /* if no suitable region is found then we need to extend the heap*/
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    
    return bp;
}

/* find a region of size asize in the heap by searching linerally from the start of the heap until the end of the heap*/
static void *find_fit(size_t asize) {
    void *bp;
    /* loop through the entire heap*/
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        /* check if each block is free and if the size is big enough*/
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    /* if we get here, no fit was found*/
    return NULL;
}

/* find the smallest possible region that can fit the size*/
static void *best_fit(size_t asize) {
    void *bp;
    void *tempp =  NULL; /* this will be used to keep track of the current best region */
    size_t hdr_size;

    /* loop through the entire heap*/
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        /* get the current header size*/
        hdr_size = GET_SIZE(HDRP(bp));

        /* check if each block is free and if the size is big enough*/
        if (!GET_ALLOC(HDRP(bp)) && (asize <= hdr_size)) {
            /* if the block is the exact size, then return immediately*/
            if (asize == hdr_size){
                return bp;
            }
            /* if this is the first region found, then change tempp*/
            if (tempp == NULL) {
                tempp = bp;
            } else {
                /* check if the region is better than any previous blocks and then update tempp*/
                if (hdr_size < GET_SIZE(HDRP(tempp))) {
                    tempp = bp;
                }
            }
        }
    }
    /* return the best fitting block*/
    return tempp;
}

/* start searching for a block of size asize from the position of the last call to malloc */
static void *next_fit(size_t asize) {
    void *bp;
    /* loop through the heap starting from the last_malloc_call*/
    for (bp = last_malloc_call; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        /* check if each block is free and if the size is big enough*/
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_malloc_call = bp; /* update the global variable*/
            return bp;
        }
    }
    
    last_malloc_call = heap_listp; /* reset pointer to the start of the heap*/
    return NULL; 
}

/* place an allocated block at bp*/
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    /* check if the difference between the size of the block and the size of the current block is greater
        than the minimum size of 16 bytes
    */
    if ((csize - asize) >= (2*DSIZE)) {
        /* we will divide the region into 2 parts and create the overhead for both regions*/
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        /* just change the block to allocated*/
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    } 
}


/*
 * mm_free - Freeing a block does nothing.
 */

void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));
    /* change the headers and footers to not be allocated*/
    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    /* call coalesce to merge with nearby free blocks*/
    coalesce(ptr);
    
}

/* check regions surrounding bp is they are free and then merge regions*/
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1, if the next region and the previous region are allocated, set last_malloc_call to freed region*/
    if (prev_alloc && next_alloc) {
        last_malloc_call = bp;
        return bp; 
    }

    /* case 2, if only the next region is free, merge those 2 regions, set last_malloc to freed region*/
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        last_malloc_call = bp;
        return(bp);
    }

    /* case 3, if only the previous region is free, merge those 2 regions, set last_malloc to freed region*/
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        last_malloc_call = PREV_BLKP(bp);
        return(PREV_BLKP(bp));
    }

    /* case 4, if previous and next regions are free, merge all three regions and set last_malloc to beginning of the block*/
    else { 
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        last_malloc_call = PREV_BLKP(bp);
        return(PREV_BLKP(bp));
    }


}

/*
 * mm_realloc - takes a pointer and size and adjusts the allocated region to the size
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; /* copy of the pointer to the old region*/
    void *oldhdr = HDRP(oldptr); /* pointer to the header of the region */
    void *newptr; /* will hold a pointer to a new region if we need to call malloc*/
    void *next_blk; /* pointer to the next block after the current region*/
    void *next_hdr; /* pointer to the header of the next block*/
    size_t size_align; /* the size aligned to nearest block*/
    size_t size_w_overhead; /* full block size including header/footer*/
    size_t next_blk_size; /* holds the size of the next block*/
    size_t old_hdr_size; /* size of the header of the original pointer*/



    if (oldptr == NULL) { /* check if the ptr is null and return malloc(size)*/
        return mm_malloc(size);
    }
    if (size <= 0) { /* check if size is valid, and then free the block*/
        mm_free(oldptr);
        return oldptr;
    }

    size_align = ALIGN(size); 
    size_w_overhead = size_align + OVERHEAD;
    old_hdr_size = GET_SIZE(oldhdr);
    
    if (size_w_overhead == old_hdr_size) { /* if the block is the same size then do nothing*/
        return oldptr;
    }
    
    next_blk = NEXT_BLKP(oldptr);
    next_hdr = HDRP(next_blk);
    next_blk_size = GET_SIZE(next_hdr);

    /* case one is if the next block is allocated*/
    if (GET_ALLOC(next_hdr)) {
        /* check if the size difference is too small to form 2 blocks */
        if  ((old_hdr_size - size_w_overhead) < 2*DSIZE)  { 
            return oldptr;
        } else if (old_hdr_size > size_w_overhead){
            PUT(oldhdr, PACK(size_w_overhead, 1)); /* change the orginal header for the correct size*/
            PUT(oldptr + size_align, PACK(size_w_overhead, 1)); /* find the new footer and change to match header */
            /* add header/footer for the newly formed block*/
            PUT((void *)((char *)oldptr + size_align + WSIZE),PACK(old_hdr_size - size_w_overhead ,0));
            PUT( FTRP(oldptr),PACK( old_hdr_size - size_w_overhead ,0));
            return oldptr;
        }
        /* second case is if the next block is unallocated*/
    } else {
        /* check to see if there is enough space between the 2 blocks to hold the full block*/
        if ((old_hdr_size > size_w_overhead) || (old_hdr_size + next_blk_size - 2*DSIZE >= size_w_overhead)) {
            PUT(oldhdr, PACK(size_w_overhead, 1)); /* change the orginal header for the correct size*/
            PUT(oldptr + size_align, PACK(size_w_overhead, 1)); /* find the new footer and change to match header */
            /*modify the next block and then change the global malloc call to the new free block*/
            PUT((void *)((char *)oldptr + size_align + WSIZE),PACK(old_hdr_size - size_w_overhead + next_blk_size ,0));
            PUT(FTRP(next_blk), PACK(old_hdr_size - size_w_overhead + next_blk_size ,0));
            last_malloc_call = NEXT_BLKP(oldptr);
            return oldptr;
        }
    }
    /* if we reach here then we know we need to call malloc for more space*/
            newptr = mm_malloc(size); 
            mm_free(oldptr); /* free the old region*/
            if (newptr == NULL) {
                return NULL;
            }
            memcpy(newptr, oldptr, size_align); /* copy to new location*/
            return newptr;
}


    

    static int mm_check(void){
        void *bp;
        void *start_heap = mem_heap_lo();
        void *end_heap = mem_heap_hi();
        int curr_block_alloc = GET_ALLOC(heap_listp);
        

        /* loop through the entire heap*/
        for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
            /* check if any free blocks are next to each other */
            if (bp != heap_listp){
                if (!GET_ALLOC(HDRP(bp)) && !curr_block_alloc) {
                    printf("there are adjacent free blocks");
                    return 0;
                } else {
                    curr_block_alloc = GET_ALLOC(HDRP(bp));
                }
            }
            /* check that things in heap only point to addresses in the heap*/
            if (bp > end_heap || bp < start_heap) {
                printf("there are addresses outside the heap");
                return 0;
            }
            /* check to see if all blocks are aligned*/
            if (GET_SIZE(HDRP(bp)) % DSIZE != 0){
                printf("there are blocks not aligned properly");
                return 0;
            }
        }
    return 1;
    }





















