/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p) ((size_t *)(((char *)(p)) - SIZE_T_SIZE))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 7)

#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define GET_SIZE(p) (GET(p) & ~0x07)
#define GET_ALLOC(p) (GET(p) & 0x01)

#define HDPR(p) (((char *)(p)) - WSIZE)
#define FTPR(p) (((char *)(p)) + GET_SIZE(HDPR(p)) - DSIZE)

#define NEXT_BLPR(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLPR(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

#define GET_PREV_PTR(p) ((char *)(p) + WSIZE)
#define GET_SUCC_PTR(p) ((char *)(p))
#define GET_PREV_VAL(p) GET(GET_PREV_PTR(p))
#define GET_SUCC_VAL(p) GET(GET_SUCC_PTR(p))
#define SET_PREV_VAL(p, val) PUT(GET_PREV_PTR(p), val)
#define SET_SUCC_VAL(p, val) PUT(GET_SUCC_PTR(p), val)

static char *free_listp;

void *find_fit(size_t size) {
    char *ptr = free_listp + GET_SUCC_VAL(free_listp);

    while (ptr != free_listp) {
        if (size <= GET_SIZE(HDPR(ptr))) 
            return ptr;
        ptr = free_listp + GET_SUCC_VAL(ptr);
    }

    return NULL;
}

void add_list(void *ptr) {   
    unsigned int succ_val = GET_SUCC_VAL(free_listp);
    
    SET_PREV_VAL(ptr, 0);
    SET_SUCC_VAL(ptr, succ_val);
    
    SET_SUCC_VAL(free_listp, ((char *)ptr) - free_listp);
    if (succ_val) 
        SET_PREV_VAL(free_listp + succ_val, ((char *)ptr) - free_listp);
}

void remove_list(void *ptr) {
    unsigned int pred_val = GET_PREV_VAL(ptr);
    unsigned int succ_val = GET_SUCC_VAL(ptr);
    
    SET_SUCC_VAL(free_listp + pred_val, succ_val);
    if (succ_val) 
        SET_PREV_VAL(free_listp + succ_val, pred_val);
}

void place(void *ptr, size_t size) {
    size_t blocksize = GET_SIZE(HDPR(ptr));

    if ((blocksize - size) < 16) {
        remove_list(ptr);
        PUT(HDPR(ptr), PACK(blocksize, 1));
        PUT(FTPR(ptr), PACK(blocksize, 1));
    } else {
        remove_list(ptr);
        PUT(HDPR(ptr), PACK(size, 1));
        PUT(FTPR(ptr), PACK(size, 1));

        ptr = NEXT_BLPR(ptr);
        PUT(HDPR(ptr), PACK(blocksize - size, 0));
        PUT(FTPR(ptr), PACK(blocksize - size, 0));
        add_list(ptr);
    }
}

void *coalesce(void *ptr) {
    void *pre = PREV_BLPR(ptr);  
    void *next = NEXT_BLPR(ptr);
    size_t size;

    if (GET_ALLOC(HDPR(pre)) && GET_ALLOC(HDPR(next))) {
        add_list(ptr);
        return ptr;
    } else if (GET_ALLOC(HDPR(pre)) && (!GET_ALLOC(HDPR(next)))) {
        remove_list(next);
        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(next));
        PUT(HDPR(ptr), PACK(size, 0));
        PUT(FTPR(ptr), PACK(size, 0));
        add_list(ptr);
        return ptr;
    } else if ((!GET_ALLOC(HDPR(pre))) && GET_ALLOC(HDPR(next))) {
        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(pre));
        PUT(HDPR(pre), PACK(size, 0));
        PUT(FTPR(pre), PACK(size, 0));
        return pre;
    } else {
        remove_list(next);
        size = GET_SIZE(HDPR(ptr)) + GET_SIZE(HDPR(pre)) + GET_SIZE(HDPR(next));
        PUT(HDPR(pre), PACK(size, 0));
        PUT(FTPR(pre), PACK(size, 0)); 
        return pre;
    }   

}

void *extend_heap(size_t words)
{
    char *ptr;
    size_t size;
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if((long)(ptr = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDPR(ptr), PACK(size, 0));
    PUT(FTPR(ptr), PACK(size, 0));
    PUT(HDPR(NEXT_BLPR(ptr)), PACK(0, 1));

    return coalesce(ptr);
}


int mm_init(void) { 

    if ((free_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) 
        return -1;

    PUT(free_listp, 0);
    PUT(free_listp + WSIZE, PACK(ALIGNMENT, 1));
    PUT(free_listp + 2 * WSIZE, PACK(ALIGNMENT, 1));
    PUT(free_listp + 3 * WSIZE, PACK(ALIGNMENT, 1));

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

void *malloc(size_t size) {
    size_t newsize;
    char *ptr;

    newsize = ALIGN(size + DSIZE);

    ptr = find_fit(newsize);
    
    if (ptr == NULL) {
        size_t extendsize = MAX(newsize, CHUNKSIZE);
        ptr = extend_heap(extendsize / WSIZE);
    }

    place(ptr, newsize);
    return ptr;
}

void free(void *ptr) {
    if (!ptr) return; 

    size_t size = GET_SIZE(HDPR(ptr));   
    PUT(HDPR(ptr), PACK(size, 0));
    PUT(FTPR(ptr), PACK(size, 0));

    coalesce(ptr);
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if (!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if (size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose) {
    /*Get gcc to be quiet. */
    verbose = verbose;
}
