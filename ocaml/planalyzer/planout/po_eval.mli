(** Module for evaluating an AST with an environment/store. *)

val eval_po_expr : Po_env.env -> Po_syntax.po_expr -> Po_syntax.po_expr
    
val sort : Po_syntax.po_aexpr -> Po_syntax.po_aexpr 

val extract_by_key : (Po_syntax.po_cexpr -> Po_syntax.po_expr -> 'b) -> 
  (Po_syntax.po_expr -> 'b) -> Po_syntax.po_cexpr -> Po_syntax.po_expr -> 
  'b

val get_num_ctor : Config.origin -> Po_syntax.getref -> string -> int -> 
  Po_syntax.po_aexpr

val get_bool_ctor : Config.origin -> Po_syntax.getref -> string -> int -> 
  Po_syntax.po_bexpr
 
val get_ctr_ctor : Po_syntax.base_type -> Config.origin -> 
  Po_syntax.getref -> string -> int -> Po_syntax.po_cexpr

val get_str_ctor : Config.origin -> Po_syntax.getref -> string -> int -> 
  Po_syntax.po_sexpr

val get_ctor : Config.origin -> Po_syntax.getref -> string -> int -> 
  Po_syntax.po_expr