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


/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 *********************************************************/

team_t team = {
    /* Team name */
    "ateam",

    /* First member's full name */
    "Harry Bovik",

    /* First member's email address */
    "bovik@cs.cmu.edu",

    /* Second member's full name (leave blank if none) */
    "",

    /* Second member's email address (leave blank if none) */
    ""
};


#define WSIZE 4
#define DSIZE 8
#define MINBLOCK 24
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define PACK(size, alloc) ((size) | (alloc))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define PREDP(bp) ((char *)(bp))
#define SUCCP(bp) ((char *)(bp) + DSIZE)
#define PRED(bp) (*(void **)(PREDP(bp)))
#define SUCC(bp) (*(void **)(SUCCP(bp)))

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))

#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


static char *heap_listp;
static char *free_listp;
static char *last_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void free_insert(void *bp);
static void free_remove(void *bp);


/*
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    free_listp = NULL;
    last_listp = NULL;
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));

    heap_listp += 2 * WSIZE;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    
    return 0;
}


static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    free_insert(bp);

    return coalesce(bp);
}


static void free_insert(void *bp)
{
    if (free_listp == NULL) {
        free_listp = bp;
        last_listp = bp;
        PRED(bp) = NULL;
        SUCC(bp) = NULL;
    }
    else {
        SUCC(last_listp) = bp; /* 기존 꼬리의 다음에 새 block을 연결해라*/
        PRED(bp) = last_listp;
        SUCC(bp) = NULL;
        last_listp = bp;
    }
}

static void free_remove(void *bp)
{
    /* 1. free block이 하나뿐인 경우 */
    if (PRED(bp) == NULL && SUCC(bp) == NULL) {
        free_listp = NULL;
        last_listp = NULL;
    }

    /* 2. 맨 앞 block을 제거하는 경우 */
    else if (PRED(bp) == NULL) {
        free_listp = SUCC(bp);
        PRED(free_listp) = NULL;
    }

    /* 3. 맨 마지막 block을 제거하는 경우 */
    else if (SUCC(bp) == NULL) {
        last_listp = PRED(bp);
        SUCC(last_listp) = NULL;
    }

    /* 4. 중간 block을 제거하는 경우 */
    else {
        SUCC(PRED(bp)) = SUCC(bp);
        PRED(SUCC(bp)) = PRED(bp);
    }

    PRED(bp) = NULL;
    SUCC(bp) = NULL;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *
 * Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE) { /* 최소블록을 24바이트로*/
        asize = 3 * DSIZE;
    }
    else {
        asize = DSIZE *
                ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);

    return bp;
}


/*
 * mm_free - Freeing a block does nothing.
 */

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    free_insert(bp);
    coalesce(bp);
}


static void *coalesce(void *bp)
{
    size_t prev_alloc;
    size_t next_alloc;
    size_t size;

    prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        free_remove(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
    }

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        free_remove(bp);
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))
              + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        free_remove(bp);
        free_remove(NEXT_BLKP(bp));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    return bp;
}


static void *find_fit(size_t asize)
{ /*
    여기서 일단 free인것을 찾고 그 값이 이제 그 bp안의 헤더로 들어가서 이제 그 헤더의 사이즈가 지금 넣으려고 하는
    size보다 더 크면 넣을 수 있게 그곳의 주소값을 가져온다.
    */
    char *bp;
    for (bp = free_listp; bp != NULL; bp = SUCC(bp)) {
        if((GET_SIZE(HDRP(bp))>= asize))
            return bp;
    }
    return NULL;
}


static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remain = csize - asize;

    free_remove(bp);

    if (remain >= MINBLOCK) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(remain, 0));
        PUT(FTRP(bp), PACK(remain, 0));

        free_insert(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_realloc(void *bt, size_t size)
{
    void *oldptr = bt;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}



