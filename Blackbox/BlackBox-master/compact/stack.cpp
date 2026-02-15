#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../interface.h"

#include "stack.h"

/*
s->top   --->........  \
             ........  |
             ........  |
             ........  |
             ........  |  -- total of s->size locations
s->fill_ptr->........  |
              data     |
s->bottom --> data     /
*/


struct stack *new_stack(int size)
{
  struct stack *s;
  int *a;

  if (size == 0) size=DEFAULT_STACK_SIZE;

  s = ((struct stack *) malloc(sizeof(struct stack)));
  if (s==NULL)  {
    fprintf(STDMSG,"Malloc failed. Exiting.\n");
    exit(1);
  }

  a = ((int *) malloc(sizeof(int)*size));
  if (a==NULL)  {
    fprintf(STDMSG,"Malloc failed. Exiting.\n");
    exit(1);
  }

  s->size = size;
  s->fill_ptr = a;
  s->bottom = a;
  s->top = &a[size-1];

  return(s);
}

void
grow_stack(struct stack *s)
{
  int *a;
  int new_size = (s->size)*2;
  int old_fill_ptr = s->fill_ptr - s->bottom;

#ifdef TRACE
  printf("Reallocating a stack.  New size: %d.\n",new_size);
#endif

#ifdef DEBUG
  printf("Stack before realloc.\n");
  print_stack(s);
#endif

  a = ((int *) realloc(s->bottom,sizeof(int)*new_size));
  if (a==NULL)  {
    fprintf(STDMSG,"Realloc failed. Old stack size %d. New stack size %d. Exiting.\n",
	    s->size,new_size);
    fflush(stdout);
    exit(1);
  }

  s->size = new_size;
  s->fill_ptr = a + old_fill_ptr;
  s->bottom = a;
  s->top = &a[new_size-1];

#ifdef DEBUG
  printf("Stack after realloc.\n");
  print_stack(s);
#endif
}

void
die_on_empty_stack(struct stack *s)
{
  fprintf(STDMSG,"Attemp to pop empty stack at %d.\n",s);
  exit(1);
}

int
stack_length(struct stack *s)
{
  return((((int) s->fill_ptr) - ((int) s->bottom))/sizeof(int));
}

void
print_stack(struct stack *s)
{
  int *p = s->bottom;
  
  printf("stack(size:%d, %d:%d:%d): ",s->size,s->bottom,s->fill_ptr,s->top);
  for(;p < s->fill_ptr;p++) printf("%d ",*p);
  printf("\n");
}

int 
stack_find(struct stack *s, int x)
{
  register int *ptr = s->bottom;
  int *top = s->fill_ptr;

  for(;ptr<top;ptr++) if ((*ptr)==x) return(1);
  return(0);
}

void
/* Delete x from stack s */
stack_delete(struct stack *s, int x)
{
  register int *ptr = s->bottom;
  int *fill = s->bottom;
  int *top = s->fill_ptr;

  for(;ptr<top;ptr++) {
    *fill = *ptr;
    if (! (*ptr == x)) fill++;}

  s->fill_ptr = fill;
}

void
/* Delete any stack element satisfying f */
stack_delete_if(struct stack *s, int (*f) (int))
{
  register int *ptr = s->bottom;
  int *fill = s->bottom;
  int *top = s->fill_ptr;

  for(;ptr<top;ptr++) {
    *fill = *ptr;
    if (! f(*ptr)) fill++;}

  s->fill_ptr = fill;
}

void
stack_delete_if(struct stack *s, int (*f) (struct stack *))
{
  register int *ptr = s->bottom;
  int *fill = s->bottom;
  int *top = s->fill_ptr;

  for(;ptr<top;ptr++) {
    *fill = *ptr;
    if (! f((struct stack *)*ptr)) fill++;}

  s->fill_ptr = fill;
}

void
stack_remove_duplicates(struct stack *s)
{
  register int *ptr = s->bottom, *ptr2;
  int *fill = s->bottom;
  int *top = s->fill_ptr;
  
  for(;ptr<top;ptr++) {
    int found_it;
    *fill = *ptr;
    found_it = 0;
    for(ptr2=ptr+1;ptr2<top;ptr2++)
      if (*ptr == *ptr2) { found_it=1; break;}
    if (! found_it) fill++;
  }

  s->fill_ptr = fill;
}

struct stack *copy_stack(struct stack *s)
{
  struct stack *ns = new_stack(s->size);
  memcpy(ns->bottom,s->bottom,s->size*sizeof(int));
  ns->fill_ptr = ns->bottom + stack_length(s);
  return(ns);
}

void copy_stack_data(struct stack *s1, struct stack *s2)
{
  int *p1;

  while (s1->size < s2->size) grow_stack(s1);

  p1 = s1->bottom;
  map_stack(s2, *(p1++) = *ptr;);
  s1->fill_ptr = p1;
}

struct stack *append (struct stack *s1, struct stack *s2)
{
  struct stack *result=copy_stack(s1);
  map_stack(s2,spush(*ptr,result));
  return(result);
}



/*  TEST CODE

print_int(x)
int x;
{
  printf("%d ",x);
}

main()
{
  struct stack *s,*s2,*s3;
  int negative();

  s = new_stack(10);

  spush(1,s);
  spush(2,s);
  spush(-2,s);
  spush(3,s);
  spush(-4,s);
  print_stack(s);
  s2 = copy_stack(s);
  printf("new stack:\n");
  print_stack(s2);
  s3 = append(s,s2);
  print_stack(s3);
  stack_delete_if(s,negative);
  stack_delete_if(s2,negative);
  print_stack(s3);
  stack_delete_if(s3,negative);
  print_stack(s3);
}

negative(x)
int x;
{
  if (x<0) return(1);
  return(0);
}

simple_test()
{
  struct stack *x;

  x = new_stack();

  fpush(3,x);
  fpush(4,x);
  print_stack(x);
  printf("Length of stack = %d\n",stack_length(x));
  printf("%d\n",fpop(x));
  printf("%d\n",fpop(x));
  print_stack(x);
  printf("Length of stack = %d\n",stack_length(x));
}

harder_test()
{
  struct stack *x;

  x = new_stack(2);

  spush(1,x);
  print_stack(x);
  spush(2,x);
  spush(3,x);
  print_stack(x);
  spush(4,x);
  spush(5,x);
  print_stack(x);
  spush(6,x);
  spush(7,x);
  spush(8,x);
  spush(9,x);
  print_stack(x);
  printf("%d\n",fpop(x));
  printf("%d\n",fpop(x));
  print_stack(x);
}


time_test()
{
  struct stack *x;
  int i;

  x = new_stack(10000000);

  for(i=0;i<10000000;i++) fpush(i,x);
  for(i=0;i<10000000;i++) fpop(x);
}
*/
