/*
 ******************************************************************************
 *                                   mm.c                                     *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                  TODO: insert your documentation here. :)
 *					        Author:Xianfu Sun
 *                         Andrew ID: xianfus
 *			Final:  Segregate Lists used LIFO policy
 *          the segregate lists are {16}, {32,64}, {64,256}
 *			{256,1024}, {1024,4096}, {>4096}
 *          maxium search time for the fitted block
 *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined (such as when running mdriver-dbg), these macros
 * are enabled. You can use them to print debugging output and to check
 * contracts only in debug mode.
 *
 * Only debugging macros with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

// Word and header size (bytes)
static const size_t wsize = sizeof(word_t);

// Double word size (bytes)
static const size_t dsize = 2 * wsize;

// Minimum block size (bytes)
// it needs at least 3 dsize because it has to store
// 2 prev and next pointer to the next free block and the header
static const size_t min_block_size = dsize;

// chunksize is the expanded size when the system
// call mem_sbrk to expand the heap
// (Must be divisible by dsize)
static const size_t chunksize = (1 << 12);

// the mask to show if a block has been allocated
static const word_t alloc_mask = 0x1;

// the mask to show if the previous block has been allocated
static const word_t pre_alloc_mask = 0x2;

// a mask to show the size of the block, header and footer included
static const word_t size_mask = ~(word_t)0xF;

// a msk to show if the block is a 16-byte-block
static const word_t special_block_mask = 0x4;

// maxium seglists
// the corresponding lists are{16}, [32,64)
//[64,256),[256,1024),[1024,4096),[4096,)
static const size_t max_list_num = 6;

/* Represents the header and payload of one block in the heap
this is only for the normal block(the block size is larger
than 16*/
typedef struct block {
  /* Header contains size + allocation flag */
  word_t header;

  /*
   zero length of the array to show the variable
   playload
   */
  union {
    struct {
      struct block *next;
      struct block *prev;
    } fPointer;
    char load[0];
  } payload;
  /*
   footers are inside the playload of the free blocks
   */
} block_t;

/*Representing 16 bytes seglist*/
typedef struct block_16 {

  /*because the address is aligned to 16 bytes so we
  only need the higher 60 bit to store the pointers
  for a free block it is used to store the pointers*/
  word_t header; // next

  /*can be used as payload: fixed-size 8 bytes
  or to store the pointer to the previous free blocks*/
  word_t footer; // prev

} block16_t;

/*block size is 32 for the normal block
16 for the 16-byte blcok*/
static const size_t blocksize = 2 * dsize;            // 32 bytes
static const size_t block_16size = sizeof(block16_t); // 16 bytes

/* Global variables */

// Pointer to first block
static block_t *heap_start = NULL;

// list of the free list
static block_t *free_list_headers[max_list_num - 1];

// start of the 16 bytes free block lists
static block16_t *header_16;

/* Function prototypes for internal helper routines */

bool mm_checkheap(int lineno);

// only return a normal block
static block_t *extend_heap(size_t size);

// only find the normal block
static block_t *find_fit(size_t asize);
static word_t *coalesce_block(word_t *header);

// only normal block need to be splited
static word_t *split_block(block_t *block, size_t asize);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool pre_alloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(word_t *header);
static size_t get_payload_size(word_t *header);

static bool extract_alloc(word_t header);
static block16_t *extract_address(word_t header);
static bool get_alloc(word_t *header);
static bool get_pre_alloc(word_t *header);

static void write_header(word_t *header, size_t size, bool pre_alloc,
                         bool alloc);
static void write_footer(word_t *header, size_t size, bool pre_alloc,
                         bool alloc);
static void write_pre_alloc(word_t *header, bool pre_alloc);
static void mark_alloc(word_t *header);

static word_t *payload_to_header(void *bp);
static void *header_to_payload(word_t *header);
static word_t *header_to_footer(word_t *block);

static word_t *find_next(word_t *header);
static word_t *find_prev_footer(word_t *block);
static word_t *find_prev(word_t *header);

static block_t *next_free(block_t *block);
static block16_t *next_free_16(block16_t *block);
static block_t *prev_free(block_t *block);
static block16_t *prev_free_16(block16_t *block);
static void write_next(block_t *src, block_t *des);
static void write_prev(block_t *src, block_t *des);
static void write_next_16(block16_t *src, block16_t *des);
static void write_prev_16(block16_t *src, block16_t *des);

static void insert_block(block_t *block, block_t *header);
static void remove_block(block_t *block);
static void append_block(block_t *block, block_t *header);
static void insert_block_16(block16_t *block);
static void remove_block_16(block16_t *block);

static size_t adapt_list(size_t N);
static block_t *search_list(block_t *header, size_t asize);
static bool is_special_block(word_t *header);
static void mark_16(word_t *header, bool flag);
static bool reach_end(word_t *header);

/*
 return true if the initialization succeed
 the initial size for the heap equals to the chunksize
 with a prologue and a epilogue
 */
bool mm_init(void) {
  /* Create the initial empty heap
  first extend the heap for the segregatre
  lists' headers and the epilogue and prologue
  for the heap*/

  char *start = (char *)(mem_sbrk(2 * dsize + (max_list_num - 1) * blocksize +
                                  block_16size));

  if (start == (void *)-1) {
    return false;
  }

  /* set up the header for the 16 bytes block
  because start is 0x80000000, we need all
  these headers meet the alignment requirements*/

  start += wsize;

  // set up all the headers for all normal seglist
  block_t *header;
  for (size_t i = 0; i < max_list_num - 1; i++) {
    header = free_list_headers[i] = (block_t *)start;

    /*initialize the free list and add the first elem
    into the free list
    the header point to itself at first*/
    write_next(header, header);
    write_prev(header, header);

    start += blocksize;
  }

  // set up for the 16 byte list
  header_16 = (block16_t *)start;

  header_16->header = (word_t)header_16 & size_mask;
  header_16->footer = (word_t)header_16 & size_mask;
  start += block_16size;
  /*
   set up the prologue and epilogue
   */
  start += wsize; // padding we need the prologue to be aligned
  word_t *prologue = (word_t *)start;
  word_t *epilogue = prologue + 1;
  *prologue = pack(0, true, true); // Heap prologue (block footer)
  *epilogue = pack(0, true, true); // Heap epilogue (block header)

  // Heap starts with first "block header", currently the epilogue
  heap_start = (block_t *)&epilogue;

  // Extend the empty heap with a free block of chunksize bytes
  if (extend_heap(chunksize) == NULL) {
    return false;
  }

  return true;
}

/*
malloc
return the void* which pointed to the allocated memory
use first fit strategy to search for a fit block
split the allocate block if it is too large
 */

void *malloc(size_t size) {

  dbg_requires(mm_checkheap(214));

  size_t asize;      // Adjusted block size
  size_t extendsize; // Amount to extend heap if no fit is found
  block_t *block;
  void *bp = NULL;

  if (heap_start == NULL) // Initialize heap if it isn't initialized
  {
    mm_init();
  }

  if (size == 0) // Ignore spurious request
  {
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
  }

  // Adjust block size to include overhead and to meet alignment requirements
  asize = round_up(size + wsize, dsize);

  /* if the request is 16 bytes, Search the 16 byte free list first
  this will terminate the process if it finds a block in the 16 byte
  block list*/
  if (asize == min_block_size) {
    block16_t *block16 = next_free_16(header_16);

    // the 16 byte list is not empty
    if (block16 != header_16) {

      word_t *new_header_16 = (word_t *)block16;
      // remove the block from the list
      remove_block_16(block16);

      // for a allocated 16 byte block, it headers
      // store the size and other information
      bool pre_alloc_16 = get_pre_alloc(new_header_16);
      write_header(new_header_16, asize, pre_alloc_16, true);

      // mark the block as 16 byte
      mark_16(new_header_16, true);

      // change the pre_alloc status of its next block
      word_t *next_header_16 = find_next(new_header_16);
      write_pre_alloc(next_header_16, true);

      bp = header_to_payload(new_header_16);
      return bp;
    } // if
  }

  // normal block allocation
  // the block size must be at least 32 bytes.
  block = find_fit(asize);

  // If no fit is found, request more memory, and then and place the block
  if (block == NULL) {
    extendsize = max(asize, chunksize);
    // extend the heap and insert the new free block to the front
    block = extend_heap(extendsize);
    if (block == NULL) // extend_heap returns an error
    {
      return bp;
    }
  }

  // The block should be marked as free
  dbg_assert(!get_alloc((word_t *)block));

  /* Mark block as allocated and its size.
  change the status of the next block
  the write_header will set the 16-byte block flag as 0*/
  word_t *new_header = (word_t *)block;
  mark_alloc(new_header);

  // change the pre-alloc status of its next block
  word_t *header_next = find_next(new_header);
  write_pre_alloc(header_next, true);

  // Try to split the block if too large
  block_t *splitBlock;
  word_t *splitHeader;
  block16_t *splitBlock_16;

  /*the split may corrupt the next or prev pointer
  of its original block (if it is a 16 byte block)
  we need to sore the information in advance*/
  size_t prev_blocksize = get_size(new_header);
  block_t *next_block = next_free(block);
  block_t *prev_block = prev_free(block);

  splitHeader = split_block(block, asize);

  if (splitHeader) {
    size_t split_size = get_size(splitHeader);
    size_t split_index = adapt_list(split_size);
    size_t old_index = adapt_list(prev_blocksize);

    // if the split block and the previous block
    // remains into the same seglist then we do the reconnect
    if (split_index == old_index && split_size != min_block_size) {

      // try to reconnect the splitted block
      splitBlock = (block_t *)splitHeader;
      write_next(splitBlock, prev_block); // prev_block->next = splitBlock
      write_next(next_block, splitBlock); // splitBlock->next = next_block
      write_prev(splitBlock, next_block); // next_block->prev = split_block
      write_prev(prev_block, splitBlock); // split_block->prev = prev_block

    } else {
      // new free block generated
      // remove the original block from its original list
      write_next(next_block, prev_block); // prev_block->next = next_block
      write_prev(prev_block, next_block); // next_block->prev = prev_block
      if (split_size == min_block_size) {

        /*a new 16 byte block generated mark this block as
         16 and change its size field to pointers*/
        splitBlock_16 = (block16_t *)splitHeader;

        word_t *footer_16 = header_to_footer(splitHeader);
        mark_16(splitHeader, true);
        mark_16(footer_16, true);
        insert_block_16(splitBlock_16);

      } else { // the new generated block is not 16 byte
        // insert the block to an appropriate seglist
        splitBlock = (block_t *)splitHeader;
        block_t *header = free_list_headers[split_index];
        insert_block(splitBlock, header);
      }
    }
  } // if splitted

  /* if no new free block generated
   remove this block from the free block list*/
  else {
    remove_block(block);
  }

  bp = header_to_payload(new_header);

  dbg_ensures(mm_checkheap(280));

  return bp;
}

/*
free the memory with a given payload pointers
try to coalesce with its neighbor free block
 */
void free(void *bp) {

  dbg_requires(mm_checkheap(289));

  if (bp == NULL) {
    return;
  }

  word_t *header = payload_to_header(bp);
  size_t size = get_size(header);

  // The block should be marked as allocated
  dbg_assert(get_alloc(header));

  // Mark the block as free
  bool pre_alloc = get_pre_alloc(header);
  word_t *footer = header_to_footer(header);
  write_header(header, size, pre_alloc, false);
  write_footer(header, size, pre_alloc, false);

  if (size == min_block_size) {
    /* if the block is 16 byte we should mark it again
     because write footer and header will reset the
         flag to zero*/
    mark_16(header, true);
    mark_16(footer, true);
  }

  // change the status of its next block
  word_t *header_next = find_next(header);
  write_pre_alloc(header_next, false);

  // Try to coalesce the block with its neighbors
  header = coalesce_block(header);

  // insert the block in the front
  size_t coalesce_size = get_size(header);
  size_t index = adapt_list(coalesce_size);
  // insert it to the 16 byte list
  if (coalesce_size == min_block_size) {

    insert_block_16((block16_t *)header);
  } else {
    // insert the block to an appropriate seglist
    block_t *list_header = free_list_headers[index];
    insert_block((block_t *)header, list_header);
  }

  dbg_ensures(mm_checkheap(313));
}

/*
malloc another block, whose size equals to the argument
copy the original memory to the new block
return the new pointer and free the old pointer
 */
void *realloc(void *ptr, size_t size) {

  word_t *header = payload_to_header(ptr);
  size_t copysize;
  void *newptr;

  // If size == 0, then free block and return NULL
  if (size == 0) {
    free(ptr);
    return NULL;
  }

  // If ptr is NULL, then equivalent to malloc
  if (ptr == NULL) {
    return malloc(size);
  }

  // Otherwise, proceed with reallocation
  newptr = malloc(size);

  // If malloc fails, the original block is left untouched
  if (newptr == NULL) {
    return NULL;
  }

  // Copy the old data
  copysize = get_payload_size(header); // gets size of old payload
  if (size < copysize) {
    copysize = size;
  }
  memcpy(newptr, ptr, copysize);

  // Free the old block
  free(ptr);

  return newptr;
}

/*
malloc a space that has at least elements*size size long
and set the memory inside to be 0
 */
void *calloc(size_t elements, size_t size) {

  void *bp;
  size_t asize = elements * size;

  if (asize / elements != size) {
    // Multiplication overflowed
    return NULL;
  }

  // size will be aligned inside malloc
  bp = malloc(asize);
  if (bp == NULL) {
    return NULL;
  }

  // Initialize all bits to 0
  memset(bp, 0, asize);

  return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 extend the heap to by adding size memory to original memory
 colase with the possible previous free block
 and return the block
 */
static block_t *extend_heap(size_t size) {
  void *bp;

  // Allocate an even number of words to maintain alignment
  // printf("extend the heap, size %zu\n", size);
  size = round_up(size, dsize);
  if ((bp = mem_sbrk(size)) == (void *)-1) {
    return NULL;
  }

  /*
   To replace the previous epilogue and change it
   into header of the new free block
   */
  word_t *new_header = payload_to_header(bp);
  bool pre_alloc = get_pre_alloc(new_header);
  write_header(new_header, size, pre_alloc, false);
  write_footer(new_header, size, pre_alloc, false);

  // Create new epilogue header and initially the
  // prealloc is false
  // because it has a new free list
  word_t *new_epilogue = find_next(new_header);
  write_header(new_epilogue, 0, false, true);

  // Coalesce in case the previous block was free
  new_header = coalesce_block(new_header);
  block_t *block = (block_t *)new_header;

  // always insert the block to the last seglist(size >= 4096)
  insert_block(block, free_list_headers[max_list_num - 2]);

  return block;
}

/* insert the block to the first of the list*/
static void insert_block(block_t *block, block_t *header) {

  write_next(next_free(header), block); // block->next = header->next
  write_prev(header, block);            // block->prev = header;
  write_prev(block, next_free(header)); // header->next->prev = block
  write_next(block, header);            // header->next = block
}

/*append the block at the tail of the list*/
static void append_block(block_t *block, block_t *header) {
  write_next(header, block);            // block->next = header
  write_prev(prev_free(header), block); // block->prev = header->prev
  write_next(block, prev_free(header)); // header->prev->next = block
  write_prev(block, header);            // header->prev = block
}

// remove the block from the free list
static void remove_block(block_t *block) {
  write_next(next_free(block),
             prev_free(block)); // block->prev->next = block->next
  write_prev(prev_free(block),
             next_free(block)); // block->next->prev = block->prev
}

/*insert an 16-byte block to the front of
the list*/
static void insert_block_16(block16_t *block) {
  write_next_16(next_free_16(header_16), block); // block->next = header->next

  write_prev_16(header_16, block); // block->prev = header-16
  write_prev_16(block,
                next_free_16(header_16)); // header_16->next->prev = block
  write_next_16(block, header_16);        // header_16->next = block
}

/*remove a 16-byte block*/
static void remove_block_16(block16_t *block) {
  write_next_16(next_free_16(block), prev_free_16(block));
  write_prev_16(prev_free_16(block), next_free_16(block));
}

/*
 coalesce the block by checking its neigbour blocks
 and return the pointer of the coalesced block
 */
static word_t *coalesce_block(word_t *header) {
  dbg_requires(!get_alloc(header));
  size_t size = get_size(header);
  word_t *result = header;

  /*
  we cannot access an allocated block
  so check the pre-alloc flag first
  and coalesce the free block
   */
  word_t *header_next = find_next(header);

  bool prev_alloc = get_pre_alloc(header);
  bool next_alloc = get_alloc(header_next);

  if (prev_alloc && next_alloc) // Case 1
  {
    // Nothing to do
  }

  else if (prev_alloc && !next_alloc) // Case 2
  {

    size_t size_next = get_size(header_next);
    size += size_next;

    // remove the original block from the list
    if (size_next == min_block_size) {
      remove_block_16((block16_t *)header_next);
    } else {
      remove_block((block_t *)header_next);
    }
    // this will set the 16 byte block flag to 0 automatically
    write_header(header, size, prev_alloc, false);
    write_footer(header, size, prev_alloc, false);

  }

  else if (!prev_alloc && next_alloc) // Case 3
  {
    word_t *header_prev = find_prev(header);

    prev_alloc = get_pre_alloc(header_prev);
    size_t prev_size = get_size(header_prev);

    size += prev_size;
    result = header_prev;

    // remove the block first
    if (prev_size == min_block_size) {
      remove_block_16((block16_t *)header_prev);
    } else {
      remove_block((block_t *)header_prev);
    }

    // this will set the 16 byte block flag to 0 automatically
    write_header(header_prev, size, prev_alloc, false);
    write_footer(header_prev, size, prev_alloc, false);

  } else // Case 4
  {
    // prev_block

    word_t *header_prev = find_prev(header);
    prev_alloc = get_pre_alloc(header_prev);
    size_t size_prev = get_size(header_prev);

    // next_block
    size_t size_next = get_size(header_next);

    size += size_next + size_prev;
    // remove the previous block from the list
    if (size_prev == min_block_size) {

      remove_block_16((block16_t *)header_prev);
    } else {
      remove_block((block_t *)header_prev);
    }

    // remove next block from the list
    if (size_next == min_block_size) {
      remove_block_16((block16_t *)header_next);
    } else {
      remove_block((block_t *)header_next);
    }
    // this will set the 16 byte block flag to 0 automatically
    write_header(header_prev, size, prev_alloc, false);
    write_footer(header_prev, size, prev_alloc, false);

    result = header_prev;
  }
  dbg_ensures(!get_alloc(header));

  return result;
}

/*
 split the block if the block is large enough to generate a new
 free block
 return the block pointer if new free block generated
 return NULL if it cannot generate new free block
 */
static word_t *split_block(block_t *block, size_t asize) {
  dbg_requires(get_alloc((word_t *)block));
  /* asize>=min_block_size and asize <= get_size(block) */

  word_t *header = (word_t *)block;
  size_t block_size = get_size(header);

  // check if the remainging block size larger than the min size
  // and change the corresponding data
  if ((block_size - asize) >= min_block_size) {
    word_t *header_next;
    word_t *header_next_next;
    bool pre_alloc = get_pre_alloc(header);
    write_header(header, asize, pre_alloc, true);

    header_next = find_next(header);
    // change the status of next block
    write_header(header_next, block_size - asize, true, false);
    write_footer(header_next, block_size - asize, true, false);

    // change the pre_allocation status to the next block
    header_next_next = find_next(header_next);
    write_pre_alloc(header_next_next, false);

    return header_next;
  } else
    return NULL;

  dbg_ensures(get_alloc(header));
}

/*
 go over the free list and check for the fitting block
 use the first fit policy to have a nice throughput performance
 */
static block_t *find_fit(size_t asize) {
  block_t *block;
  block_t *aheader;
  size_t index;

  /*find an apprpriate list index to
  begin the searching*/
  index = adapt_list(asize);

  /*starrt from the most ideal list
  we check the larger list if no fit
  was found in the current list*/
  while (index < max_list_num - 1) {
    aheader = free_list_headers[index];
    block = search_list(aheader, asize);
    // found a block
    if (block) {
      return block;
    }
    // try another free list
    index++;
  }
  return NULL; // no fit found
}

/*given a requested size, return an appropriate
list index to start the fit search.
the corresponding checkpoint for the seglist is
16, 32, 64, 256, 1024, 4096*/
static size_t adapt_list(size_t size) {
  // we should check at least the lower 6 bit
  size_t bias = 6;
  size_t check = bias;
  size_t i = 0;

  for (i = 0; i < max_list_num - 2; i++) {
    // if size < 2^check)
    if ((size >> check) == 0) {
      return i;
    }
    check += 2;
  }
  // return the index of the last list
  return max_list_num - 2;
}

/*with a given free list header search the list, return
NULL if no fit block is found*/
static block_t *search_list(block_t *header, size_t asize) {
  block_t *block;
  for (block = next_free(header); block != header; block = next_free(block)) {
    if (get_size((word_t *)block) >= asize) {
      return block;
    }
  }

  return NULL; // no fit found
}

/*
check the invariant of the structure
 */
bool mm_checkheap(int line) {
  void *lo = mem_heap_lo();
  void *hi = mem_heap_hi();
  word_t *header = (word_t *)heap_start;
  size_t free_list_num = 0;
  size_t size;
  // go over all the heap
  while (reach_end(header)) {
    header = find_next(header);
    dbg_assert(((size_t)header % dsize) == wsize); // check address alignment
    word_t *next_header = find_next(header);
    size = get_size(header);
    dbg_assert(round_up(size, dsize) == size); // check size
    dbg_assert(size >= min_block_size);
    // if this is a allocated block
    if (get_alloc(header)) {
      dbg_assert(get_pre_alloc(next_header) == true); // check next header

    } else { // if it is a free block
      free_list_num++;
      dbg_assert(get_pre_alloc(next_header) == false); // check next header
      // no consecutive free blocks
      dbg_assert(get_alloc(next_header));
      dbg_assert(get_pre_alloc(header));
      // check header and footer consistency
      word_t *footer = header_to_footer(header);
      if (size != min_block_size)
        dbg_assert(*header == *footer);
    }
  }
  // check the 16 byte block
  block16_t *free_16;
  for (free_16 = next_free_16(header_16); free_16 != header_16;
       free_16 = next_free_16(free_16)) {
    free_list_num--;
    // check the range of the pointer
    dbg_assert((size_t)free_16 >= (size_t)lo);
    dbg_assert((size_t)free_16 <= (size_t)hi);
    // check it is a free block
    dbg_assert(!get_alloc((word_t *)free_16));
    // they are all marked as 16 byte
    dbg_assert(is_special_block((word_t *)free_16));
    // check the consistency of the pointer
    dbg_assert(next_free_16(prev_free_16(free_16)) == free_16);
    dbg_assert(prev_free_16(next_free_16(free_16)) == free_16);
  }
  // check other normal free blocks
  block_t *free_header;
  size_t index;
  for (index = 0; index < max_list_num - 2; index++) {
    block_t *list_header = free_list_headers[index];
    for (free_header = next_free(list_header); free_header != list_header;
         free_header = next_free(free_header)) {
      free_list_num--;
      dbg_assert((size_t)free_header >= (size_t)lo); // check the pointers range
      dbg_assert((size_t)free_header <= (size_t)hi);
      dbg_assert(!get_alloc((word_t *)free_16)); // check it is a free block
      // check the consistency of the pointer
      dbg_assert(next_free(prev_free(free_header)) == free_header);
      dbg_assert(prev_free(next_free(free_header)) == free_header);
      // check the size of the block is in correct range
      size = get_size((word_t *)free_header);
      dbg_assert(index == adapt_list(size));
    }
  }
  dbg_assert(free_list_num ==
             0); // the free list num is consistent through two checks
  return true;
}

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ba c1 e1 52 13 0a               *
 *                                                                           *
 *****************************************************************************
 */

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) { return (x > y) ? x : y; }

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n) {
  return n * ((size + (n - 1)) / n);
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool pre_alloc, bool alloc) {
  word_t tmp = (pre_alloc << 1) | alloc;
  return size | tmp;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word) { return (word & size_mask); }

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(word_t *header) {
  bool is_16 = *header & special_block_mask;
  return (is_16) ? min_block_size : *header & size_mask;
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static size_t get_payload_size(word_t *header) {
  size_t asize = get_size(header);
  return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word) { return (bool)(word & alloc_mask); }

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(word_t *header) { return *header & alloc_mask; }

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(word_t *header, size_t size, bool pre_alloc,
                         bool alloc) {
  dbg_requires(header != NULL);
  *header = pack(size, pre_alloc, alloc);
}

/*
 * write_footer: given a block's header and its size and allocation
 * and preallocation status,writes an appropriate value to the block
 * footer by first computing the position of the footer.
 */
static void write_footer(word_t *header, size_t size, bool pre_alloc,
                         bool alloc) {
  dbg_requires(header != NULL);
  dbg_requires(get_size(header) == size && size > 0);
  word_t *footerp = header_to_footer(header);
  *footerp = pack(size, pre_alloc, alloc);
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static word_t *find_next(word_t *header) {
  dbg_requires(header != NULL);
  dbg_requires(get_size(header) != 0);
  return (word_t *)((char *)header + get_size(header));
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(word_t *header) {
  // Compute previous footer position as one word before the header
  return header - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static word_t *find_prev(word_t *header) {
  dbg_requires(header != NULL);
  dbg_requires(get_size(header) != 0);
  word_t *footerp = find_prev_footer(header);
  size_t size = get_size(footerp);
  return (word_t *)((char *)header - size);
}

/*mark a given header as allocated*/
static void mark_alloc(word_t *header) { *header = *header | alloc_mask; }

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static word_t *payload_to_header(void *bp) {
  return (word_t *)((char *)bp - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(word_t *header) {
  return (void *)((char *)header + wsize);
}

/*
 * header_to_footer: given a block pointer, returns a pointer to the
 *                   corresponding footer.
 */
static word_t *header_to_footer(word_t *header) {
  return (word_t *)((char *)header + get_size(header) - wsize);
}

// return the pointer to the next free block
static block_t *next_free(block_t *block) {
  return (block_t *)block->payload.fPointer.next;
}

// return the pinter to the previous free block
static block_t *prev_free(block_t *block) {
  return (block_t *)block->payload.fPointer.prev;
}

// write the next field of a free block
// des is the block you want to change
// src is the source pointer
static void write_next(block_t *src, block_t *des) {
  des->payload.fPointer.next = src;
}

// similar to write_next
static void write_prev(block_t *src, block_t *des) {
  des->payload.fPointer.prev = src;
}

// get the allocation status of the previous block
static bool get_pre_alloc(word_t *header) {
  return (*header & pre_alloc_mask) >> 1;
}

// change the allocation status of the block without
// changing any other header information
static void write_pre_alloc(word_t *header, bool pre_alloc) {
  *header =
      (pre_alloc) ? *header | pre_alloc_mask : *header & (~pre_alloc_mask);
}

/*extract the address with a given header or footer of
a 16 byte block every block should be aligned to 0xXXXXXX8
because of the address alignment requirements*/
static block16_t *extract_address(word_t word) {
  return (block16_t *)((word & size_mask) + 0x8);
}

/*return the address of the next free 16-byte block with a
given address*/
static block16_t *next_free_16(block16_t *block) {
  return extract_address(block->header);
}

/*return the address of the previous free 16-byte block with a
given block*/
static block16_t *prev_free_16(block16_t *block) {
  return extract_address(block->footer);
}

/*write the high 60 bit of the header*/
static void write_next_16(block16_t *src, block16_t *des) {
  des->header = ((des->header) & ~size_mask) | ((word_t)src & size_mask);
}

/*write the high 60 bit of the 16 byte block's footer*/
static void write_prev_16(block16_t *src, block16_t *des) {
  des->footer = ((word_t)src & size_mask) | ((des->footer) & ~size_mask);
}

/*with a given header, return true if it is a 16_byte_block*/
static bool is_special_block(word_t *header) {
  return (bool)(*header & special_block_mask);
}

/*with a given header mark the header as 16 byte*/
static void mark_16(word_t *word, bool flag) {
  *word = flag ? (*word | special_block_mask) : (*word & ~special_block_mask);
}

/*check if the given header is the epilogue of the heap*/
static bool reach_end(word_t *header) {
  return get_alloc(header) && !get_size(header);
}