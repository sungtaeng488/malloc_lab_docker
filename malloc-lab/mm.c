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
#define MINBLOCK 16
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
#define SUCCP(bp) ((char *)(bp) + WSIZE)
#define PRED(bp) (GET(PREDP(bp)) == 0 ? NULL : OFFSET_ADDRESS(GET(PREDP(bp))))

#define SUCC(bp)  (GET(SUCCP(bp)) == 0 ? NULL : OFFSET_ADDRESS(GET(SUCCP(bp))))
#define offset(bp) (char *)(bp) - heap_listp
#define OFFSET_ADDRESS(off) (heap_listp + (off))

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
        PUT(PREDP(bp), 0);
        PUT(SUCCP(bp), 0);
        last_listp = bp;
        free_listp = bp;
    }
    else {
    PUT(PREDP(bp), 0);                       // bp.pred = NULL
    PUT(SUCCP(bp), offset(free_listp));      // bp.succ = 기존 head
    PUT(PREDP(free_listp), offset(bp));      // 기존 head.pred = bp
    free_listp = bp;                         // bp가 새 head
    }
}

static void free_remove(void *bp)
{
    /* 1. 하나뿐인 경우 */
    if (GET(PREDP(bp)) == 0 && GET(SUCCP(bp)) == 0) {
        free_listp = NULL;
        last_listp = NULL;
    }

    /* 2. 맨 앞 - 리스트에서는 맨뒤 */
    else if (GET(PREDP(bp)) == 0) {
        free_listp = OFFSET_ADDRESS(GET(SUCCP(bp)));
        PUT(PREDP(free_listp), 0);
    }

    /* 3. 맨 뒤  - 리스트에서는 맨 앞*/
    else if (GET(SUCCP(bp)) == 0) {
        void *pred = OFFSET_ADDRESS(GET(PREDP(bp)));
        PUT(SUCCP(pred), 0);
        last_listp = pred;
    }

    /* 4. 중간 */
    else {
        void *pred = OFFSET_ADDRESS(GET(PREDP(bp)));
        void *succ = OFFSET_ADDRESS(GET(SUCCP(bp)));

        PUT(SUCCP(pred), GET(SUCCP(bp)));
        PUT(PREDP(succ), GET(PREDP(bp)));
    }

    PUT(PREDP(bp), 0);
    PUT(SUCCP(bp), 0);
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

    if (size <= DSIZE) {
        asize = 2* DSIZE;
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
    if (bp == NULL) {
        return;
    }
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
{
    char *bp;

    for (bp = free_listp; bp != NULL;) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }

        size_t next_offset = GET(SUCCP(bp));
        bp = next_offset ? OFFSET_ADDRESS(next_offset) : NULL;
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

void *mm_realloc(void *bp, size_t size)
{
    void *newptr;
    void *oldptr = bp;
    size_t copySize;
    size_t asize;
    size_t old_size;
    if (bp == NULL)
        return mm_malloc(size);

    if (size == 0) {
        mm_free(bp);
        return NULL;
    }

    /* malloc과 똑같이 실제 필요한 block size 계산 */
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    }
    else {
        asize = DSIZE *
                ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    old_size = GET_SIZE(HDRP(bp));

    /* 1. 기존 block 크기로 이미 충분하면 그대로 사용 */
    if (old_size >= asize)
        return bp;


    /* 다음 block이 free인 경우 */
    if (GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0) {

        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size_t total = old_size + next_size;

        /* 현재 block + 다음 free block으로 충분한 경우 */
        if (total >= asize) {

            /* next는 이제 free block이 아니므로 free list에서 제거 */
            free_remove(NEXT_BLKP(bp));

            /* 기존 bp를 확장된 allocated block으로 변경 */
            PUT(HDRP(bp), PACK(total, 1));
            PUT(FTRP(bp), PACK(total, 1));

            return bp;
        }
    }
    /* 아무것도 아닌경우는 새로 malloc을 해서 거기에 채움 - 기존*/

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

