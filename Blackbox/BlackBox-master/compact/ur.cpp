#include <stdio.h>
#include <ctype.h>

#include "tab.h"
#include "stack.h"
#include "compact.h"

extern int level;
extern struct stack *ur_stack;
extern struct var *var_array;
extern signed char *val;
extern struct stack *undo;

extern struct stack *to_branch;
extern signed char to_branch_flag;


int value(int x)
{
  int var,s;

  if (x>0) {s=1;var=x;} else {s=-1;var=-x;}

#ifdef TRACE
  printf("%d ",x);
#endif
  if (val[var]==0) {
#ifdef OTHER_COUNTS
    (*vars_valued)++;
#endif
    val[var]=s;
    return(ur(x));
  }
  else return(val[var]==s);
}


/*
This is like value but pushes onto the stack instead of
recursively calling ur.
*/
int internal_value(int x)
{
  int var,s;

  if (x>0) {s=1;var=x;} else {s=-1;var=-x;}

#ifdef TRACE
  printf("%d ",x);
#endif
  if (val[var]==0) {
#ifdef OTHER_COUNTS
    (*vars_valued)++;
#endif
    val[var]=s;
    fpush(x,ur_stack);
    return(1);
  }
  else return(val[var]==s);
}


/* Put this before ur so that we can inline it. */
inline static int walk_clause(struct stack *s)
{
  map_stack(s,if(val[abs(*ptr)]==0) return(internal_value(*ptr)));

  /* at this point every term in clause has a value */
  map_stack(s,if(val[abs(*ptr)] == sign(*ptr)) return(1));

#ifdef TRACE
  printf("No unvalued lits in clause: ");
  print_stack(s);
  printf("\n");
#endif
  return(0);
}


#define decf_count(p) {spush(((int) &(p)),undo); (p)--;}

int ur(int x)
{
  int *ur_stack_ptr; /* points to the next lit to be ur'ed */

  ur_stack_ptr = make_empty(ur_stack); /* ur_stack_ptr set to bottom of stack */
  fpush(x,ur_stack);

  while(! (ur_stack_ptr == ur_stack->fill_ptr)) {
    int x = *ur_stack_ptr++;
    register int *ptr;
    struct var xs;
    struct stack *hits,*clauses;
    int *top;
    struct clause *c;

    if (x<0) {
      xs = var_array[-x];
      hits = xs.neg_hits; clauses = xs.pos_clauses;
    }
    else {
      xs = var_array[x];
      hits = xs.pos_hits; clauses = xs.neg_clauses;
    }

    top = hits->fill_ptr; /* cash this out since it does not change */
    for(ptr=hits->bottom; ptr < top; ptr++)  /* map over the stack hits */
      if (!internal_value(*ptr)) return(0);
      
    top = clauses->fill_ptr;
    for(ptr=clauses->bottom; ptr < top; ptr++) {
      c = ((struct clause *) *ptr);
      decf_count(c->terms);
      if (c->terms == 1) {if (!walk_clause(c->text)) return(0);}
      else if (to_branch_flag && (c->terms == 2)) map_stack(c->text,spush(*ptr,to_branch););
    }
  }

  return(1);
}


int occurs(int i)
{
  if (i > 0) {return(occurs_pos(i));}
  else return(occurs_neg(-i));
}


int occurs_pos(int i)   /* returns 1 iff i occurs positively in an irredundant clause */
{
  struct var *is = &var_array[i];
  register int *ptr;
  int *top;
  struct clause *c;

#ifdef TRACE
  printf("Occurs check on %d.  ",i);
#endif
    
  top = (is->neg_hits)->fill_ptr;
  for(ptr=(is->neg_hits)->bottom; ptr<top; ptr++)
    if (val[abs(*ptr)] == 0) {
#ifdef TRACE
      printf("%d occurs in binary clause with %d.\n",i,*ptr);
#endif
      return(1);
    }
    
  top = (is->pos_clauses)->fill_ptr;
  for(ptr=(is->pos_clauses)->bottom; ptr<top; ptr++) {
    c = ((struct clause *) *ptr);
    if (! COM_redundant(c->text)) {
#ifdef TRACE
      printf("%d occurs in clause ",i);
      print_stack(c->text);
      printf("\n");
#endif
      return(1);
    }
  }
    
#ifdef TRACE
  printf("%d does not occur.\n",i);
#endif
  return(0);
}

int occurs_neg(int i)   /* returns 1 iff i occurs negatively in an irredundant clause */
{
  struct var *is = &var_array[i];
  register int *ptr;
  int *top;
  struct clause *c;

#ifdef TRACE
  printf("Occurs check on %d.",-i);
#endif
  
  top = (is->pos_hits)->fill_ptr;
  for(ptr=(is->pos_hits)->bottom; ptr<top; ptr++)
    if (val[abs(*ptr)] == 0)  {
#ifdef TRACE
      printf("%d occurs in binary clause with %d.\n",-i,*ptr);
#endif
      return(1);
    }
    
  top = (is->neg_clauses)->fill_ptr;
  for(ptr=(is->neg_clauses)->bottom; ptr<top; ptr++) {
    c = ((struct clause *) *ptr);
    if (! COM_redundant(c->text)) {
#ifdef TRACE
      printf("%d occurs in clause ",-i);
      print_stack(c->text);
      printf("\n");
#endif
      return(1);
    }
  }
    
#ifdef TRACE
  printf("%d does not occur.\n",-i);
#endif
  return(0);
}


int COM_redundant(struct stack *s)
{
  map_stack(s,if(val[abs(*ptr)]==sign(*ptr)) return(1));
  return(0);
}
