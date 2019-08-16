(********************************************************************************
  ASTNormalize module
  - Runs constant propagation
  - Minimizes the program (reducing arithmetic and boolean expressions)
  - Rewrites non-booleans in guards as booleans
  - Extracts from guards:
    + indexing expressions
    + relations
    + functions
  - Refines types for top-level CustomExprs, Iexprs, Coalesces, and Gets.
 ******************************************************************************)
module type Normalize = sig

  type program = Po_syntax.program 
  type env

  module POConfig : Config.Config with type basetype = Po_syntax.base_type 
  type typequals

  exception Empty_domain of Po_syntax.po_expr [@@deriving sexp]
  exception Static_unit_error of string * Po_syntax.po_expr
  exception Unit_constant of Po_syntax.po_expr 

  val reset_varid : unit -> unit
  val reset_skipid : unit -> unit 

  val skipid : unit -> string 

  val tree_rewrite : ?breadth:bool ->
                     ?astfn:(Po_syntax.ast_node -> Po_syntax.ast_node) ->
                     ?efn:(Po_syntax.po_expr ->    Po_syntax.po_expr) ->
                     ?afn:(Po_syntax.po_aexpr ->   Po_syntax.po_aexpr) ->
                     ?bfn:(Po_syntax.po_bexpr ->   Po_syntax.po_bexpr) ->
                     ?cfn:(Po_syntax.po_cexpr ->   Po_syntax.po_cexpr) ->
                     ?sfn:(Po_syntax.po_sexpr ->   Po_syntax.po_sexpr) ->
                     program -> program


  (** Entry point for normalization. *)
  val normalize : typequals -> program -> (typequals * program)

  (** Runs constant propagation. Run twince during normalization. *)
  val constant_propagation : (typequals * program) -> (typequals * program)

  (** Minimize and normalize the arithmetic and boolean operations. *)
  val minimize_program : (typequals * program) -> (typequals * program)

  (** Runs constant_propagation and minimize_program until the program no 
  longer changes. *)
  val constant_min_steady : (typequals * program) -> (typequals * program)

  (** Infers the types of nodes when possible. *)
  val specialize_steady : varid:(unit -> string) -> (typequals * program) -> 
    (typequals * program)

  (** For an expression, iteratively extract all nested function applications 
  as single function applications, returning a list of fresh variable names 
  and single assignments. e.g. expression
  
      fn(arr[i] + 10)

      linearizes to

      [(fv1, arr[i]); (fv2, fv1 + 10); (fv3, fn f2)]        

    *)
  val linearize_fn_app : varid:(unit -> string) -> (typequals * program) -> 
    (typequals * program)

  val linearize_steady : varid:(unit -> string) -> (typequals * program) -> 
    (typequals * program)

  (** Random variables that are used in expressions with explicit salts 
  should be lifted above the expression and defined using the salt as the 
  assignment name. Does not allow the salt to share a variable name with any \
  other variables in the program. *)
  val lift_random_variables : varid:(unit -> string) ->
    (typequals * program) -> (typequals * program)

  (* The PlanOut JS compiler converts else statements to something that looks 
  like a Lisp cond with the guard equal to true. When there is no else-branch,
  we add one that has no statements in its consequent. *)
  val add_default_guard : skipid:(unit -> string) -> (typequals * program) -> 
    (typequals * program)

  val minimize_seqs : skipid:(unit -> string) -> (typequals * program) -> 
    (typequals * program)

end 

module MakeNormalize (
    POCfg : Config.Config with type basetype = Po_syntax.base_type
) : Normalize 
    with type typequals = POCfg.typequals
    and module POConfig = POCfg
