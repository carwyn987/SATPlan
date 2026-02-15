#ifndef __BBIO_H__
#define __BBIO_H__

void print_defpredicate ();
void print_ctrl_file_header ();
void print_paren_end ();
void print_verified_rules ();
void print_rule (int rule_type);
void load_rule (int rule_type);
void open_control_file ();
#endif
