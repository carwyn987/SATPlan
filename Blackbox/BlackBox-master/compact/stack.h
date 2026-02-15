#define DEFAULT_STACK_SIZE 100

struct stack {
  int size;
  int *fill_ptr;  /* Points to the next location on the stack */
  int *top;       /* Points to the very top location on the stack */
  int *bottom;    /* Points to the very bottom location on the stack */
};

/* #define STACK_DEBUG 1 */

struct stack *new_stack(int size);
void grow_stack(struct stack *s);
void die_on_empty_stack(struct stack *s);
int stack_length(struct stack *s);
void print_stack(struct stack *s);
int stack_find(struct stack *s, int x);
void stack_delete(struct stack *s, int x);
void stack_delete_if(struct stack *s, int (*f) (int));
void stack_delete_if(struct stack *s, int (*f) (struct stack *));
void stack_remove_duplicates(struct stack *s);
struct stack *copy_stack(struct stack *s);
void copy_stack_data(struct stack *s1, struct stack *s2);
struct stack *append (struct stack *s1, struct stack *s2);

/* fpush and fpop are the "fast" versions of the stack operations.
No error checking is done.  No check is done to make sure there is
room on the stack.
*/

#define empty_stack(s) ((s)->fill_ptr == (s)->bottom)
#define make_empty(s) (s->fill_ptr = s->bottom)

#define fpush(x,s) *(s->fill_ptr)++ = x
#define fpop(s) *(--(s->fill_ptr))
#define ftop(s) *((s->fill_ptr)-1)
#define fsecond(s) *((s->fill_ptr)-2)
#define fthird(s) *((s->fill_ptr)-3)

#define spush(x,s) {if ((s)->fill_ptr > (s)->top) grow_stack(s); *((s)->fill_ptr)++ = ((int) x);}
#define spop(x,s) (? (s->fill_ptr == s->bottom) die_on_empty_stack(s) : *(--(s->fill_ptr)))

/* The first argument to this macro is the body of the for loop.
   The current stack element is accessed by *ptr. */
#define map_stack(s,x) {register int *ptr; int *top = (s)->fill_ptr; for(ptr=(s)->bottom;ptr<top;ptr++) {x;}}
