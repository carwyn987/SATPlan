#ifndef __LEARN_C_
#define __LEARN_C_

#include "tim.h"

#define LEARN_CONTROL		0x0001
#define VERIFY_CONTROL		0x0002
#define REMOVE_DUMMY		0x0004
#define MAX_NUM_EXAMPLE		300
#define MAX_NUM_TABLE_EXAMPLE	MAX_NUM_EXAMPLE*2
#define MAX_NUM_ATTRIBUTE	8
#define MAX_NUM_PRED_VAR	4
#define GAIN_FACTOR		0.9
#define NODE_COVERED		-127
#define MAX_GAIN		1000.0  
#define NO_GAIN			-1000.0	/* used when pos + neg == 0 */
#define MAX_NUM_RULE_BODY_LITERAL	3


enum EXAMPLE_TYPE { NEG_EX = -1, NO_EX, POS_EX };
enum VAR_TYPE { OLD_VAR, NEW_VAR };
enum BINDING_TYPE { NO_BINDING = -2, FREE_BINDING = -1 };
enum LITERAL_TYPE { NO_LIT, PRED_LIT, NOT_PRED_LIT, EQUAL_LIT, UNEQUAL_LIT, 
		    CONST_LIT, NOT_CONST_LIT };
enum BACKGROUND_KNOWLEDGE_TYPE {DYNAMIC, STATIC, GOAL};
enum LITERAL_SEARCH_TYPE { FIND_LIT, ADD_DET_LIT, ADD_NEWVAR_LIT };

typedef struct LITERAL {
  char *lit_name; 		/* could be a predicate or a constant */
  int lit_type;			/* literal type */
  int changed;		
  int bk_type;			/* backgroun knowledge type */
  int num_var;	
  int binding[MAX_NUM_PRED_VAR + 1];	/* [0] useless */
  int bind_type[MAX_NUM_PRED_VAR + 1];   
  int rule_lit_type;		/* rule literal type */
  struct LITERAL *next;
} literal_elt, *literal_ptr;

typedef struct LEARNED_RULE {
  literal_ptr body;
  struct LEARNED_RULE *next;
} learned_rule_elt, *learned_rule_ptr;

propspace_ptr
find_property_space (char *name, int i);
char* seperate_string (char *src, char *dest);
void learn ();

#endif
