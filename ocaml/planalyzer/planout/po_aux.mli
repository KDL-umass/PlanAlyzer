(** Dependencies:
    - Po_syntax 
    - Po_env 
  *)

(** This module contains auxiliary/helper functionality for PlanOut AST queries 
    and manipulation. *)

(** The type of the environment, where values and terminal expressions are 
    kept *)
type env

(** The module used to hold type information. *)
module Types : Map.S with type key = string 

(** The type of the set. *)
type varidset = Config.Params.t

val sexp_of_varidset : varidset -> Sexplib.Sexp.t
val varidset_of_sexp : Sexplib.Sexp.t -> varidset


(****************** Extracting variables from ASTs ******************)

(** This is the base function for selecting out different types of variables. 
    AST- and type-based restrictions can be provided using the optional input 
    functions (asdfn, efn, afn, befn, cfn, and sfn). See the implementation of 
    get_guard_vars for an example. *)
val get_node_vars : ?astfn:(Po_syntax.ast_node -> bool) -> 
                    ?efn:(Po_syntax.po_expr -> bool) -> 
                    ?afn:(Po_syntax.po_aexpr -> bool) -> 
                    ?bfn:(Po_syntax.po_bexpr -> bool) -> 
                    ?cfn:(Po_syntax.po_cexpr -> bool) -> 
                    ?sfn:(Po_syntax.po_sexpr -> bool) -> 
                    Po_syntax.ast_node -> varidset

(** Function that returns all variable definitions and references. Note: it 
    will include references to externally defined variables, but not externally 
    defined functions. Functions are not first-class objects in PlanOut. *)
val get_program_vars : Po_syntax.program -> varidset

(** Function that returns all of the variables used in the guards of a program's
    conditional statements. *)
val get_guard_vars : Po_syntax.program -> varidset

 (** Returns all of the variables used or defined along the input path 
     through the program. *)
val get_path_vars : Po_syntax.ast_node list -> varidset

(** Returns all of the assigned variables and their indices. *)
val get_all_assignments : Po_syntax.ast_node -> varidset

(** Predicate testing whether a given input variable has been defined. Note 
    that this function takes the variable's name and not the varidkey, which 
    includes an index referring to the particular version of a variable. *)
val is_var_in_program : Po_syntax.program -> string -> bool

(******** Extracting type and type qualifier information from ASTs ********)

(** Test whether the input expression calls an external function and 
    returns the name of the function if so. For example, when called on the AST 
    expression corresponding to the input code:

        customNumberExpression(userid=userid, myKey="asdf")

    the function returns `Some "customNumberExpression"`. Note that if a custom 
    expression is used inside a larger expression (e.g., `1 + customNumberFn
    (userid=userid, myKey="asdf"`, it will return None.)*)
val expr_external : Po_syntax.po_expr -> string option

(** Returns the expression type of the input expression. Note that this 
    function does not run type inference. *)
val get_expression_type : Po_syntax.po_expr -> Po_syntax.base_type

(** Returns the type of the codomain of the list. *)
val get_type_of_list : Po_syntax.po_expr list -> Po_syntax.base_type

(** Returns the type of the codomain of the input. *)
val get_codomain : ?env:Po_env.env -> Po_syntax.po_expr -> 
    Po_syntax.base_type

(** Tests whether the supplied choices correspond to True/False or 0/1. *)
val is_bernoulli_trial : choices:Po_syntax.po_cexpr -> bool

(** Tests whether the weights supplied are all equivalent. Note that this 
    function does not evaluate PlanOut expressions, so the expressions must be 
    structurally equivalent as well as numerically equivalent to return true. *)
val is_uniform_choice : weights:Po_syntax.po_cexpr -> bool

(** Tests whether the input expression is a constant. *)
val is_constant : Po_syntax.po_expr -> bool

(** Tests whether the input expression is a random variable. *)
val is_random_variable : Po_syntax.po_expr -> bool

(** Tests whether the input expression is a random integer. *)
val is_random_integer : weights:Po_syntax.po_cexpr -> 
    choices:Po_syntax.po_cexpr -> 
    (Po_syntax.po_aexpr option * Po_syntax.po_aexpr option)

(** Tests whether the input expression is null. *)
val is_null : Po_syntax.po_expr -> bool 

(** Tests whether the input expression is a phi node. *)
val is_phi : Po_syntax.po_expr -> bool

(** Tests whether the input is a function (as opposed to a constant or a 
    relation.) *)
val is_function : Po_syntax.po_expr -> bool 

(** Tests whether the input is a logical relation (e.g., equality). *)
val is_relation : Po_syntax.po_expr -> bool

(******** Extracting subtrees from ASTs ********)

(** Searches forthe first subtree satisfying the predicate defined in 
    `find_fn`. If no subtree satisfies this predicate, the function returns 
    None. This function only operates on statements, not expressions. *)
val get_ast_subtree : find_fn:(Po_syntax.ast_node -> bool) -> Po_syntax.ast_node -> 
  Po_syntax.ast_node option
    
(** Returns the sub-expression satisfying the input predicates. Since 
    expressions have types, a predicate for each type must be supplied. Default
    predicates return false (i.e., do not select the expression. Typed 
    expressions are wrapped to make them untyped upon return. *)
val get_sub_expr : ?efn:(Po_syntax.po_expr -> bool) ->
                   ?afn:(Po_syntax.po_aexpr -> bool) ->
                   ?bfn:(Po_syntax.po_bexpr -> bool) ->
                   ?cfn:(Po_syntax.po_cexpr -> bool) ->
                   ?sfn:(Po_syntax.po_sexpr -> bool) ->
                   Po_syntax.po_expr -> Po_syntax.po_expr option 
    
(** For an input variable name and index and an input program, return its 
    type. *)
val infer_var_type : ?match_on_index:bool -> Config.ssa_id -> 
    Po_syntax.program -> Po_syntax.base_type  

val resolve_type : Po_syntax.po_expr -> Po_syntax.base_type list Types.t ref -> 
    string -> Po_syntax.base_type

val add_type : Po_syntax.base_type list Types.t ref -> string ->
    Po_syntax.base_type -> unit 

val flatten_seqs : Po_syntax.ast_node list -> Po_syntax.ast_node list 