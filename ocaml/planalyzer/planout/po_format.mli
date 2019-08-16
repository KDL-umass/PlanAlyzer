(** Returns the pretty-printed string representation of an expression. Typed 
    expressions will need to be wrapped. *)
val string_of_expr : ?show_index:bool -> Po_syntax.po_expr -> string 

(** Returns the pretty-printed string representation of a program. *)
val string_of_program : ?show_index:bool -> Po_syntax.program -> string 

(** Returns the pretty-printed random op info (i.e., unit arg and salt) *)
val ast_string_of_rand : Po_syntax.rand_info option -> string 

(** This function prints out a string representation of an AST that can be 
    copied and pasted into a test case. *)
val ast_string_of_program : Po_syntax.program -> string 

(** Prints out the code for an expression that can be copied and pasted into
    a test case. *)
val ast_string_of_expr : Po_syntax.po_expr -> string 