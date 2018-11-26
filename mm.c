/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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

/* 
 * mm_init - initialize the malloc package.
 */

#define WSIZE 4 /*word and header / footer size */
#define DSIZE 8 /*double word size*/
#define CHUNKSIZE (1<<12) /*extend heap by this amount /initial free blcok and heap extend of basic size*/
/*#define SSIZE 24*/ /*6WORD to make code with explicilt list*/
#define MAX(x,y) ((x)>(y)?(x) :(y))
#define MIN(x,y) ((x)<(y)?(x) :(y))

#define PACK(size, alloc) ((size)|(alloc)) /*pack a size and allocated bit into a word, integrate size and allocate bit that can be stored in header and footer*/
#define GET(p) (*(unsigned int *)(p))/*p is void* type and GET : return the word by reading p's reference*/
#define PUT(p, val) (*(unsigned int *)(p) = (val))/* store the val where p points.*/
/*read and write a word at address p*/

/*read the size and allocated fields from address p*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) &0x1)

/*given block ptr bp, compute address of its header and footer*/
#define HDRP(bp) ((char *)(bp) -WSIZE)
#define FTRP(bp) ((char *)(bp)+ GET_SIZE(HDRP(bp))-DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))
/*#define NEXT_FREE(bp) (*(void **)(bp+DSIZE))
#define PREV_FREE(bp) (*(void **)(bp))*/
static char *heap_listp=0;
/*static char *free_listp = 0;*/
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
/*static void insert(void *bp);
static void remove(void *bp);*/

int mm_init(void)
{/*before call mm_mmaloc and mm_free, we have to initialize the heap by calling mm_init*/
	/*create the initial empty heap*/
	if((heap_listp = mem_sbrk(4*WSIZE))==(void *)-1)
		return -1;
	/*bring 4word from memory system and initialize them to  make empty free list*/
	PUT(heap_listp, 0);/*alignment padding*/
	PUT(heap_listp+WSIZE, PACK(DSIZE,1));/*header of prologue block, minimum size is 24bytes*/
	PUT(heap_listp+(2*WSIZE),PACK(DSIZE, 1));/*header of previous*/
	PUT(heap_listp+(3*WSIZE),PACK(DSIZE,1));/*header of next*/
/*	PUT(heap_listp+SSIZE, PACK(SSIZE, 1));*//*Payload shoule be satified the double word alignment, so payload is filled in 4th word so we have to current put footer in 5th word, in other words, there are 5words in heap*/
	/*PUT(heap_listp+WSIZE+SSIZE, PACK(0,1));*/ /*information of status (alloc/free) of epliogue block by using epilogue header*/
	
	heap_listp = heap_listp+(2*WSIZE);
	/*Extend the empty heap with a free block of CHUNKSIZE bytes*/
	if (extend_heap(CHUNKSIZE/WSIZE) ==NULL)
		return -1;
	return 0;

}

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/*allocate an even number of words to maintain alignment*/
	size = (words %2) ? (words+1)*WSIZE : words*WSIZE ;
	/*if(size<SSIZE)
		size = SSIZE;*/
	if((long)(bp = mem_sbrk(size))==-1)
		return NULL;
	/*initialize free block header/footer and the epilogue header*/
	PUT(HDRP(bp), PACK(size, 0)); /*free block header*/
	PUT(FTRP(bp), PACK(size, 0));/*free blcok footer*/
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));/*new epilogue header*/

	/*coalesce if the previous block was free*/
	return coalesce(bp);
}
static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if(prev_alloc && next_alloc){/*prev alloc, next alloc*/
		return bp;
	}
	else if(prev_alloc && !next_alloc){/*prev alloc, next free*/
		size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size,0));
		PUT(FTRP(bp), PACK(size,0));
	}
	else if(!prev_alloc && next_alloc){/*prev free next alloc*/
		size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size,0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		bp= PREV_BLKP(bp);
	}
	else{/*prev free next free*/
		size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
	}
	return bp;
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
	
	if(size==0)
		return NULL;
	
	if(size<=DSIZE)
		asize = 2*DSIZE;
	
	else
		asize = DSIZE*((size+(DSIZE)+(DSIZE-1))/DSIZE);
	
	if((bp = find_fit(asize))!=NULL){
		place(bp, asize);
		return bp;
	}

	extendsize=MAX(asize, CHUNKSIZE);
	if((bp=extend_heap(extendsize/WSIZE))==NULL)
		return NULL;
	place(bp, asize);
	return bp;
}

static void *find_fit(size_t asize)
{
	void *bp;
	for(bp=heap_listp;GET_SIZE(HDRP(bp))>0; bp=NEXT_BLKP(bp)){
		if(!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp)))){
			return bp;
		}
	}
	return NULL;	
}

static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));

	if((csize-asize)>=(2*DSIZE)){
		PUT(HDRP(bp), PACK(asize,1));
		PUT(FTRP(bp), PACK(asize,1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize,0));
		PUT(FTRP(bp), PACK(csize-asize,0));
	}
	else{
		PUT(HDRP(bp), PACK(csize,1));
		PUT(FTRP(bp), PACK(csize,1));
	}
}

/*static void insert(void *bp)
{
	if(free_listp == NULL){
		PREV_FREE(bp) = NULL;
		NEXT_FREE(bp) = NULL;
		free_listp = bp;
	}
	PREV_FREE(bp) = NULL;
	NEXT_FREE(bp) = free_listp;
	PREV_FREE(free_listp) = bp;
	free_listp = bp;
}

static void remove(void *bp)
{
	if(free_listp ==NULL)
		return;

	//free block is in the middle of free_list*/
/*	if(PREV_FREE(bp)!=NULL &&NEXT_FREE(bp)!=NULL){
		NEXT_FREE(PREV_FREE(bp))=NEXT_FREE(bp);
		PREV_FREE(NEXT_FREE(bp))=PREV_FREE(bp);
	}
	//free block is in the front of free_list*/
/*	else if(PREV_FREE(bp)==NULL && NEXT_FREE(bp)!=NULL){
		PREV_FREE(NEXT_FREE(bp))=NULL;
		free_listp = NEXT_FREE(bp);
	}
	//free block is at the end of free_list*/
/*	else if(PREV_FREE(bp)!=NULL && NEXT_FREE(bp)==NULL){
		NEXT_FREE(PREV_FREE(bp)) = NULL;
	}	
	//there is only one free block in the free_list*/
/*	else if(PREV_FREE(bp)==NULL && NEXT_FREE(bp)==NULL){
		free_listp = 0;
	}	
}*/
/*	
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
	size_t size = GET_SIZE(HDRP(ptr));
	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    	void *oldptr = ptr;
    	void *newptr;
    	size_t copySize;
    	if(oldptr ==NULL)
		return mm_malloc(size);
	if(size==0){
		mm_free(oldptr);
		return NULL;
	}
	
   	newptr = mm_malloc(size);
    	if (newptr == NULL)
      		return NULL;
    	/*copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);*/
	copySize = MIN(size, GET_SIZE(HDRP(oldptr)) - SIZE_T_SIZE);
    	if (size < copySize)
      		copySize = size;
    	memcpy(newptr, oldptr, copySize);
    	mm_free(oldptr);
    	return newptr;
}














