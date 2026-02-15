#ifndef __COMPACT_H_
#define __COMPACT_H_

/* functions in compact.c */
void new_level();
void end_level();
void blast_var(int x);
int check_lit(int x);
void pure_literal_rule();
void unlink_deleted_clauses();
int clause_deleted(int x);
void init_tab(int numvararg);
int unary_failed_lit();
int binary_failed_lit(int itlimit);
void blast_clause(struct clause* c);
int check_singleton(int x);
int contains_var_x(struct stack *s);
void delete_clause(struct clause *c);
int maybe_resolve(struct stack *text, int x);
void dump_no_renum(int * wff, int * newnumclause);
int resolve_singletons();
int resolve_against(struct stack *text, int x);

/* functions in input.c */
int read_int(int *x);
int try_assign(int x);
int assert_clause(struct stack *text);
struct stack *clause_get(struct stack **s);
int opposite_val(int x);
int cleanup_clause(struct stack *text);

/* functions in ur.c */
int value(int x);
int internal_value(int x);
int ur(int x);
int occurs(int i);
int occurs_pos(int i);
int occurs_neg(int i);
int COM_redundant(struct stack *s);

#endif
