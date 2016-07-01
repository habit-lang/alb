#include <stdio.h>
#include <stdlib.h>

#define HEAP_SIZE (1024 * 128)

/////////////////// External functions exported by cheney

/* Allocates a heap of 'size' bytes and initializes toStartp, toEndp, frStartp, frEndp, and freep.
   A heap of 'size' bytes involves three malloc'ed arreas of 'size' bytes each.
 */
extern int cheney_init_heap(int size);

/* Allocates 'len' 4-byte cells from the heap.
   'root' is the pointer to the stack listing the GC-roots. */
extern int cheneyAlloc (int len, int root);

extern char* toStartp;
extern char* toEndp;
extern char* frStartp;
extern char* frEndp;
extern char* freep;

///////////////

/* GC and heap checking */
int toggle = 0;

static void check_bounds() {
  if ((freep >= frStartp) && (freep <= frEndp))
    return;
  printf("bound error ");
  printf("-> toS=%x toE=%x frS=%x frE=%x free=%x\n",
          (unsigned int)toStartp, (unsigned int)toEndp, (unsigned int)frStartp, (unsigned int)frEndp, (unsigned int)freep);
  abort();
}

typedef struct {
  int fields;
  int atomic_fields;
} gc_desc;

/* don't check the last 'ignore' words allocated, because they may
 not have been initialized yet. */
static void check_heap (int ignore)  
{
  check_bounds();
  // printf ("CSTART = %x, CEND = %x\n",(unsigned int)CSTART,(unsigned int)CEND);
  char *c = frStartp;
  while (c < freep-ignore*4) {
    gc_desc *desc = (gc_desc *)(*((int *)c));
/*    if (desc < CSTART || desc > CEND - 1)
      printf ("at %x: header desc pointer %x out of range\n",(unsigned int)c,(unsigned int)desc);
    if ((((int) desc) - ((int) CSTART)) % sizeof(gc_desc) != 0)
      printf ("at %x: header desc pointer %x not aligned %lu\n",(unsigned int)c,(unsigned int)desc,sizeof(gc_desc));
  */
  int fields = desc->fields;
    int atfields = desc->atomic_fields;
    if (fields < 1) 
      printf("at %x: header desc pointer %x: impossible number of fields %d\n",(unsigned int)c,(unsigned int)desc,fields);
    if (atfields > fields)
      printf("at %x: header desc pointer %x: fields: %d, atomic fields: %d\n",(unsigned int)c,(unsigned int)desc,fields,atfields);
    c+= 4;
    int i;
    for (i = 0; i < fields; i++) {
      if (i >= atfields) {
	char *target = (char *) (*((int *) c));
	if (target) {
	  if (target < (frStartp+4) || target >= frEndp-4)
	    printf("at %x (field %d of (%d,%d)) out of range target %x\n",(unsigned int)c,i,fields,atfields,(unsigned int)target);
	  desc = (gc_desc *)(*((int *)(target-4)));
/*	  if (desc < CSTART || desc > CEND-1)
	    printf ("at %x (field %d of (%d,%d)) : target %x header desc pointer %x out of range\n",(unsigned int)c,i,fields,atfields,(unsigned int)target,(unsigned int)desc);
	  if ((((int) desc) - ((int) CSTART)) % sizeof(gc_desc) != 0)
	    printf ("at %x (field %d of (%d,%d)) : target %x header desc pointer %x not aligned\n",(unsigned int)c,i,fields,atfields,(unsigned int)target,(unsigned int)desc);
*/
	}
      }
      c +=4;
    } 
  }
  // printf("OK\n");
  toggle = 0;
}

///////////////// Entry points from cheney

/* Called at the start of 'cheneyCollect' from inside 'cheneyAlloc'.  Generally used for status and debugging. */
void gc_alarm_start() 
{
}

/* Called at the end of 'cheneyCollect' from inside 'cheneyAlloc'.  Generally used for status and debugging. */
void gc_alarm(int live)
{
  toggle = 1;
}

///////////////// Entry points from GCminor

/* The actual entry point from GCminor.  Called when the heap needs to be initialized. */
int init_heap() {
  int status = cheney_init_heap(HEAP_SIZE);
  if (status != 0)  {
    fprintf(stderr, "Heap initialization failed.\n");
    exit (status);
  }
  check_heap(0);
  return status;
}

/* The actual entry point from GCminor.  Called  */
int alloc_raw_space (int root, int len) 
{
  // printf("a:%x %d\n",root,len); 
  check_bounds();
  int r = cheneyAlloc(len,root);
  // printf("(%d)-> %x\n",len,r); 
  if (r == 0) {
    printf("OUT OF MEMORY\n");
    abort();
  }
  if (toggle) check_heap(len);
  return r;
}

/* Called when the program encounters Eerror */
void fidget_error() {
  fprintf(stderr,"Fidget program encountered Eerror\n");
  abort();
}
