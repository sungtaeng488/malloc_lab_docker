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
#define MIN(x, y) ((x) < (y) ? (x) : (y))

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
    char *minbp = NULL;
    size_t base = 0;

    for (bp = free_listp; bp != NULL;) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            if(base == 0){
                base = GET_SIZE(HDRP(bp));
                minbp = bp;
            }
            else{
                if(base> GET_SIZE(HDRP(bp))){
                    base = GET_SIZE(HDRP(bp));
                    minbp = bp;

                }
            }
        }

        size_t next_offset = GET(SUCCP(bp));
        bp = next_offset ? OFFSET_ADDRESS(next_offset) : NULL;
    }
    return minbp;
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

    /* realloc(NULL, size) == malloc(size) */
    if (bp == NULL)
        return mm_malloc(size);

    /* realloc(bp, 0) == free(bp) */
    if (size == 0) {
        mm_free(bp);
        return NULL;
    }


    /* 실제 필요한 block size 계산 */
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    }
    else {
        asize = DSIZE *
                ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }


    old_size = GET_SIZE(HDRP(bp));


    /*
     * 0. 현재 block만으로 이미 충분한 경우
     *
     * 남는 공간이 MINBLOCK 이상이면 split해서
     * utilization도 챙김
     */
    if (old_size >= asize) {

        size_t remain = old_size - asize;

        if (remain >= MINBLOCK) {

            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));

            void *remain_bp = NEXT_BLKP(bp);

            PUT(HDRP(remain_bp), PACK(remain, 0));
            PUT(FTRP(remain_bp), PACK(remain, 0));

            free_insert(remain_bp);
            coalesce(remain_bp);
        }

        return bp;
    }


    /* 현재 block의 앞/뒤 상태 */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));


    /*
     * 1. 앞 ALLOC / 뒤 FREE
     *
     * [ALLOC][ CURRENT ][ FREE ]
     */
    if (prev_alloc && !next_alloc) {

        void *next_bp = NEXT_BLKP(bp);

        size_t next_size = GET_SIZE(HDRP(next_bp));
        size_t total = old_size + next_size;

        if (total >= asize) {

            free_remove(next_bp);

            size_t remain = total - asize;

            if (remain >= MINBLOCK) {

                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));

                void *remain_bp = NEXT_BLKP(bp);

                PUT(HDRP(remain_bp), PACK(remain, 0));
                PUT(FTRP(remain_bp), PACK(remain, 0));

                free_insert(remain_bp);
            }
            else {
                PUT(HDRP(bp), PACK(total, 1));
                PUT(FTRP(bp), PACK(total, 1));
            }

            return bp;
        }
    }


    /*
     * 2. 앞 FREE / 뒤 ALLOC
     *
     * [ FREE ][ CURRENT ][ALLOC]
     */
    else if (!prev_alloc && next_alloc) {

        void *prev_bp = PREV_BLKP(bp);

        size_t prev_size = GET_SIZE(HDRP(prev_bp));
        size_t total = prev_size + old_size;

        if (total >= asize) {

            /*
             * prev free block을 이제 allocated 영역으로
             * 사용할 것이므로 free list에서 제거
             */
            free_remove(prev_bp);


            /*
             * bp가 앞으로 이동하므로 기존 payload 이동
             */
            copySize = MIN(old_size - DSIZE, size);

            memmove(prev_bp, bp, copySize);


            size_t remain = total - asize;

            if (remain >= MINBLOCK) {

                PUT(HDRP(prev_bp), PACK(asize, 1));
                PUT(FTRP(prev_bp), PACK(asize, 1));

                void *remain_bp = NEXT_BLKP(prev_bp);

                PUT(HDRP(remain_bp), PACK(remain, 0));
                PUT(FTRP(remain_bp), PACK(remain, 0));

                free_insert(remain_bp);
            }
            else {
                PUT(HDRP(prev_bp), PACK(total, 1));
                PUT(FTRP(prev_bp), PACK(total, 1));
            }

            return prev_bp;
        }
    }


    /*
     * 3. 앞 FREE / 뒤 FREE
     *
     * [ FREE ][ CURRENT ][ FREE ]
     *
     * back  = 현재 + 뒤
     * front = 앞 + 현재
     * three = 앞 + 현재 + 뒤
     *
     * asize를 만족하면서 가장 적게 남는 방법 선택
     */
    else if (!prev_alloc && !next_alloc) {

        void *prev_bp = PREV_BLKP(bp);
        void *next_bp = NEXT_BLKP(bp);

        size_t prev_size = GET_SIZE(HDRP(prev_bp));
        size_t next_size = GET_SIZE(HDRP(next_bp));


        size_t back_remain = 0;
        size_t front_remain = 0;
        size_t three_remain = 0;

        int back_ok = 0;
        int front_ok = 0;
        int three_ok = 0;

        int choice = 0;


        /* 현재 + 뒤 */
        if (old_size + next_size >= asize) {

            back_ok = 1;

            back_remain =
                old_size + next_size - asize;
        }


        /* 앞 + 현재 */
        if (prev_size + old_size >= asize) {

            front_ok = 1;

            front_remain =
                prev_size + old_size - asize;
        }


        /* 앞 + 현재 + 뒤 */
        if (prev_size + old_size + next_size >= asize) {

            three_ok = 1;

            three_remain =
                prev_size + old_size + next_size - asize;
        }


        /*
         * 가장 적게 남는 방법 선택
         *
         * 동점이면 back 우선
         * → bp 주소 유지
         * → memmove 필요 없음
         */
        if (back_ok &&
            (!front_ok || back_remain <= front_remain) &&
            (!three_ok || back_remain <= three_remain)) {

            choice = 1;       /* 현재 + 뒤 */
        }

        else if (front_ok &&
                 (!back_ok || front_remain < back_remain) &&
                 (!three_ok || front_remain <= three_remain)) {

            choice = 2;       /* 앞 + 현재 */
        }

        else if (three_ok) {

            choice = 3;       /* 앞 + 현재 + 뒤 */
        }


        /*
         * choice 1
         *
         * [FREE][CURRENT][FREE]
         *                ^^^^
         *                뒤쪽만 먹음
         */
        if (choice == 1) {

            size_t total = old_size + next_size;
            size_t remain = total - asize;

            free_remove(next_bp);

            if (remain >= MINBLOCK) {

                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));

                void *remain_bp = NEXT_BLKP(bp);

                PUT(HDRP(remain_bp), PACK(remain, 0));
                PUT(FTRP(remain_bp), PACK(remain, 0));

                free_insert(remain_bp);
            }
            else {
                PUT(HDRP(bp), PACK(total, 1));
                PUT(FTRP(bp), PACK(total, 1));
            }

            return bp;
        }


        /*
         * choice 2
         *
         * [FREE][CURRENT][FREE]
         *  ^^^^^^^^^^^^^^
         *  앞 + 현재 사용
         *
         * next free는 allocation에 사용하지 않음
         */
        else if (choice == 2) {

            size_t total = prev_size + old_size;
            size_t remain = total - asize;

            free_remove(prev_bp);

            copySize = MIN(old_size - DSIZE, size);

            memmove(prev_bp, bp, copySize);


            if (remain >= MINBLOCK) {

                PUT(HDRP(prev_bp), PACK(asize, 1));
                PUT(FTRP(prev_bp), PACK(asize, 1));

                void *remain_bp = NEXT_BLKP(prev_bp);

                PUT(HDRP(remain_bp), PACK(remain, 0));
                PUT(FTRP(remain_bp), PACK(remain, 0));

                /*
                 * remain 바로 뒤에는 기존 next free가 있으므로
                 * 둘을 다시 coalesce 해줘야 함
                 */
                free_insert(remain_bp);
                coalesce(remain_bp);
            }
            else {
                PUT(HDRP(prev_bp), PACK(total, 1));
                PUT(FTRP(prev_bp), PACK(total, 1));
            }

            return prev_bp;
        }


        /*
         * choice 3
         *
         * [FREE][CURRENT][FREE]
         *  ^^^^^^^^^^^^^^^^^^^^
         *  세 block 모두 사용
         */
        else if (choice == 3) {

            size_t total =
                prev_size + old_size + next_size;

            size_t remain = total - asize;


            /* 양쪽 free block 모두 사라짐 */
            free_remove(prev_bp);
            free_remove(next_bp);


            /* 시작 주소가 prev_bp로 이동 */
            copySize = MIN(old_size - DSIZE, size);

            memmove(prev_bp, bp, copySize);


            if (remain >= MINBLOCK) {

                PUT(HDRP(prev_bp), PACK(asize, 1));
                PUT(FTRP(prev_bp), PACK(asize, 1));

                void *remain_bp = NEXT_BLKP(prev_bp);

                PUT(HDRP(remain_bp), PACK(remain, 0));
                PUT(FTRP(remain_bp), PACK(remain, 0));

                free_insert(remain_bp);
            }
            else {
                PUT(HDRP(prev_bp), PACK(total, 1));
                PUT(FTRP(prev_bp), PACK(total, 1));
            }

            return prev_bp;
        }
    }


    /*
     * 4. 주변 block을 이용해서 확장 불가능
     *
     * 새 block을 malloc
     * → find_fit의 best-fit 사용
     * → 데이터 복사
     * → 기존 block free
     */
    newptr = mm_malloc(size);

    if (newptr == NULL)
        return NULL;


    copySize = MIN(old_size - DSIZE, size);

    memcpy(newptr, oldptr, copySize);

    mm_free(oldptr);

    return newptr;
}