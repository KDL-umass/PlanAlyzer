module type Corepo_input_lang  = sig
    type cpo_expr  
    type cpo_bexpr  
    type cpo_uexpr  
    type basetype  

    val string_of_cpo_expr : cpo_expr -> string 
    val string_of_cpo_bexpr : cpo_bexpr -> string 
end

module type Corepo_lang = sig 
    type inlang_expr 
    type prop = Not of prop 
                | And of prop * prop
                | Or of prop * prop
                | Id of Config.ssa_id 
                | True | False
    type qualifiers = {
      card : Config.cardinality;
      dyn  : Config.dynamism;
      rand : Config.randomness;
      corr : Config.corr_t
    } [@@deriving make]
    type node = 
      Assign of Config.origin * Config.ssa_id * qualifiers * inlang_expr 
      | Assert of prop 
      | Declare of Config.ssa_id * qualifiers * Smtlib.sort option 
      | Return of prop 
    type pi = node list 
    type program = pi list  
  end 

module type Min_ctxt_sig = sig            
    type key 
    type +'a t 
    val mem : key -> 'a t -> bool 
    val find : key -> 'a t -> 'a
    val add : key -> 'a -> 'a t -> 'a t 
    val empty : 'a t
    val bindings : 'a t -> (key * 'a) list 
    val cardinal : 'a t -> int 
    val remove : key -> 'a t -> 'a t 
    val keys : 'a t -> key list 
  end 

module type Corepo = sig 
    include Corepo_lang
    type typequals 
    type graph
    module Delta : Map.S with type key = string
    module Sigma : Map.S with type key = string
    module Phi : Set.S with type elt = inlang_expr
    module OriginMap : Map.S with type key = Config.ssa_id
    val origin_map : Config.origin OriginMap.t ref 

    type theta = Oratio.ratio

    type treatment = inlang_expr Delta.t * theta * Phi.t 
    type cond_set = inlang_expr Sigma.t * Phi.t
    type semantic_tuple = (treatment list) * cond_set

    val toggle_mock : unit -> bool

    module Format : sig 
        open Sexplib.Conv
        val string_of_program : program -> string 
        val string_of_path : pi -> string 
        val string_of_node : node -> string 
        val string_of_cond_set : cond_set -> string 
        val string_of_treatment : treatment -> string 
        val string_of_phi : Phi.t -> string 
        val string_of_semantics_tuples : semantic_tuple list -> string 
        (* val sexp_of_program : program -> Sexplib.Sexp.t *)
        val string_of_id : Config.ssa_id -> string 
        val string_of_inlang_expr : inlang_expr -> string 
        val string_of_qualifier : qualifiers -> string 

        val ast_string_of_path : pi -> string 
        val ast_string_of_program : program -> string 
        val ast_string_of_cond_set : cond_set -> string 
      end 

    module SMT : sig 
      val handle_sigchild : int -> unit
      end

    val eval : typequals -> graph -> program -> semantic_tuple list 
    val is_path_logged : pi -> bool 
    val delta_key_from_node : node -> string option 
    val merge_equivalent_conditioning_sets : semantic_tuple list -> 
      semantic_tuple list 
    val get_phi_varnames : Phi.t -> string list 

    module Static_errors : Exceptions.Staticbug 
      with type node = node
      and type pi = pi 
      and type cpo_expr = inlang_expr 
  
  end

module Make(Cpo : sig 
    include Corepo_input_lang
    module Ctxt : Min_ctxt_sig with type key = Config.ssa_id
    module POCfg : Config.Config with type basetype = basetype
    module PODdg : Ddg.Ddg with type key = Config.ssa_id
    type typequals = POCfg.typequals
    type graph = PODdg.outer
    val smt : string
    val mock : bool
    val max_choices : int ref
    val id_of_base_type : ?aux_args:(basetype list) -> basetype -> 
      Smtlib.sort option
    val expr_to_term : cpo_expr -> Smtlib.term
    val term_to_expr : Smtlib.term -> cpo_expr
    val is_constant : cpo_expr -> bool 
    val is_random : cpo_expr -> bool
    val randomly_split_worlds : typequals -> cpo_expr -> 
      (cpo_expr * Oratio.ratio) list 
    val eval_cpo_expr : cpo_expr Ctxt.t -> cpo_expr -> cpo_expr
    val get_expr_vars : cpo_expr -> Config.ssa_id list 
    val identifier_of_ssa_id : Config.ssa_id -> Smtlib.identifier
    val get_expr_type : ?var:(Config.ssa_id option) -> cpo_expr -> basetype
    val and_expr : cpo_expr -> cpo_expr -> cpo_expr 
    val negate_expr : cpo_expr -> cpo_expr 
    val condition_on : cpo_expr -> cpo_expr Ctxt.t -> bool
    val is_final : cpo_expr -> bool 
    val to_eq_rel : Config.ssa_id -> cpo_expr -> cpo_expr 
    val replace_gets : cpo_expr Ctxt.t -> cpo_expr -> cpo_expr 
    val ast_string_of_id : Config.ssa_id -> string
    val ast_string_of_inlang_expr : cpo_expr -> string 
    val get_delta_key : Config.ssa_id -> string 
    val get_final_binding : Config.ssa_id -> cpo_expr Ctxt.t -> cpo_expr
    val external_function : cpo_expr -> 
        (Smtlib.identifier * Smtlib.sort list * Smtlib.sort) option
    val is_pred : cpo_expr -> bool 
    val cpo_expr_compare : cpo_expr -> cpo_expr -> int 
    val is_opaque : cpo_expr -> bool   
    val is_disjunction : cpo_expr -> bool  
    val is_phi : cpo_expr -> bool 
    val is_external_function : cpo_expr -> bool 
  end) : Corepo 
    with type inlang_expr = Cpo.cpo_expr 
    and type typequals = Cpo.typequals
    and type graph = Cpo.PODdg.outer