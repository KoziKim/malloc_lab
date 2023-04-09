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
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email ADDR */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email ADDR (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// 얼라인먼트는 블록 하나 크기, 몇블록 줄 지 생각해야 됨.
// 반올림해서 할당해야함.
// ~0x7 111 -> 세자리만 0이 되고 &연산자 하면 8로 나누는 연산임.
// (size + 7) // 8
// size 주어졌을 때, 사이즈에 맞는 블록의 개수, 올림.
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// OR 비트 연산, alloc 은 0 아니면 1, size는 할당할 블록 사이즈
// 비트 연산 하면 합쳐진 숫자가 나올 것.
// PACK이 하는 일은 블록 사이즈랑 allocation 정보를 둘이 따로 나타냄
// 사이즈랑 할당됐는지 더해주는 것.
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

// put을 헤더랑 풋터에 정보를 넣을때만 쓸거임.
// p가 블록의 시작 위치.
// value 값은 PACK 해서 나온 결과물을 쓸 거임.
// 4바이트 만큼만 읽고 쓰겠다는 것.
/* Read and write a word at ADDR p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from ADDR p */
// & ~0x7 하위 3개 비트를 자른 값
// get_size 하면 해당 블록의 크기가 나옴.
// get_alloc 은 32비트에서 맨 아래 하나만 떼오겠다는 것. 할당 여부 파악.
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// 계산하기 위해 (char *) 쓴 거임.
/* Given block ptr bp, compute ADDR of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// PREV_BLKP 에서 풋터에서 3개 비트 자르면 블록 크기 나옴.
/* Given block ptr bp, compute ADDR of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define PUT_NEXT_ADDR(bp, address) (*(unsigned int *)(bp) = (address)) /* 현재 블록 포인터에 NEXT 주소를 설정함 */
#define PUT_PREV_ADDR(bp, address) (*(unsigned int *)((char *)bp + WSIZE) = (address))

#define NEXT_FREE(bp) (*(unsigned int *)(bp))          /* 다음 프리 블록의 주소 */
#define PREV_FREE(bp) (*(unsigned int *)(bp + WSIZE))  /* 이전 프리 블록의 주소 */

void*   heap_listp;
unsigned int*   ROOT;
void    take_off_from_freelist(void *bp);
void    insert_in_first_place(void *bp);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
/* 맨 앞 맨 뒤 블록 검사 안하려고, 예외처리 빼려고 프롤로그 헤더/풋터, 에필로그 헤더 넣는 거임.*/
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);                     /* 블록 포인터가 헤더 끝난 부분에서 시작 */

    ROOT = mem_heap_lo();
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* 앞 뒤 검사해서 free인 것 합침 */
/* 연결하기 전에 변수 3개 선언 */
/* size는 현재 가리키고 있는 블록 사이즈 */
/* 위 2개는 전 후 할당 됐는지 파악 */
void    take_off_from_freelist(void *bp)
{
    if (bp == ROOT) {
        ROOT = NEXT_FREE(bp);
    } 
    else {
        PUT_NEXT_ADDR(PREV_FREE(bp), NEXT_FREE(bp));
        if (NEXT_FREE(bp) != mem_heap_lo()) {
            PUT_PREV_ADDR(NEXT_FREE(bp), PREV_FREE(bp));
        }
    }
}

void    insert_in_first_place(void *bp)
{
    PUT_NEXT_ADDR(bp, ROOT); /* bp의 NEXT에 ROOT 주소 넣음*/
    if (ROOT != mem_heap_lo()) {
        PUT_PREV_ADDR(ROOT, bp); /* ROOT의 PREV에 bp 주소 넣음 */
    }
    // PUT_PREV_ADDR(bp, NULL); /* bp의 PREV에 NULL 넣음 */
    ROOT = bp; /* ROOT를 bp 주소로 바꿔줌 */
}

static void *coalesce(void *bp)
{
    // printf("c1?\n\n");
    // printf("프롤로그 헤더에 적힌 사이즈: %u\n\n", GET((char *)mem_heap_lo() + 4));
    // printf("프롤로그 풋터에 적힌 사이즈: %u\n\n", GET((char *)mem_heap_lo() + 8));
    // printf("bp의 주소: %u--- mem_heap_lo의 주소: %u\n\n", bp, mem_heap_lo());
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // printf("여기?\n\n");
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // printf("여기2?\n\n");
    size_t size = GET_SIZE(HDRP(bp));
    /* Case 1 전 후 둘 다 할당됐다면 */
    // printf("c2?\n\n");
    if (prev_alloc && next_alloc)
    {
        insert_in_first_place(bp);
        return bp;
    }
    /* Case 2 이전꺼 막힘, 다음께 free 블록 */
    /* 사이 값은 trash 값 되기 때문에 굳이 안건드림 */
    /* 헤더 먼저 바꿔야 size 만큼 이동돼서 성립 */
    else if (prev_alloc && !next_alloc)
    {
        take_off_from_freelist(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        insert_in_first_place(bp);
    }
    /* Case 3 앞이 free 블록 뒤는 할당 블록 */
    else if (!prev_alloc && next_alloc)
    {
        take_off_from_freelist(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        insert_in_first_place(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);    
    }
    /* Case 4 */
    else
    {
        take_off_from_freelist(PREV_BLKP(bp));
        take_off_from_freelist(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        insert_in_first_place(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // printf("c3?\n\n");
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;
    for (bp = ROOT; bp != mem_heap_lo(); bp = NEXT_FREE(bp))
    {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
    }
    return NULL; /* No fit */
}



static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) /* 쪼개졌을 때 */
    {
        take_off_from_freelist(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
        insert_in_first_place(NEXT_BLKP(bp));
    }
    else /* 쪼개지지 않았을 때 */
    {
        take_off_from_freelist(bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
/*  */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); /* (DSIZE - 1)은 올림 위함. size + DSIZE가 헤더 풋터 포함한 진짜 필요한 사이즈. */
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
/* 블록은 찾지 않아도 될 듯 */
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

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - 2*WSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
