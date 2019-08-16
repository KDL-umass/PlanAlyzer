module type Corepo_input_lang  = sig
    open Sexplib.Conv
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

module Corepo_lang_impl (Input_lang : Corepo_input_lang) = struct
    open Sexplib.Conv
    include Input_lang
    type inlang_expr = Input_lang.cpo_expr
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
        Assign of Config.origin * Config.ssa_id * qualifiers * cpo_expr 
        | Assert of prop 
        | Declare of Config.ssa_id * qualifiers * Smtlib.sort option 
        | Return of prop 
    type pi = (node list) 
    type program = (pi list) 
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
    (* val delta_equals : inlang_expr Delta.t -> bool  *)

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
    type graph =  PODdg.outer
    val smt : string
    val mock : bool
    val max_choices : int ref
    val id_of_base_type : ?aux_args:(basetype list) -> basetype -> 
      Smtlib.sort option
    val expr_to_term : cpo_expr -> Smtlib.term
    val term_to_expr : Smtlib.term -> cpo_expr 
    val is_constant : cpo_expr -> bool 
    (*val is_random : cpo_expr -> bool*)
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
    val is_phi : cpo_expr -> bool 
    val is_external_function : cpo_expr -> bool 
  end) = struct
    open Sexplib.Conv
    module Ctxt = Cpo.Ctxt
    module Lang = Corepo_lang_impl(Cpo)
    module Static_errors = Exceptions.Make(Lang)
    include Lang
    (* module T = struct 
        type t = Config.Params.elt 
        let compare = Config.Params.compare 
      end *)
    module Delta = Map.Make(String)
    module Sigma = Map.Make(String) 
    module Phi = Set.Make(struct 
      type t = inlang_expr 
      let compare = Cpo.cpo_expr_compare         
      end)
    module OriginMap = Map.Make(struct 
      type t = Config.ssa_id
      let compare = Config.ssa_id_compare 
    end) (* ssa_id -> origin *)
    let origin_map = ref OriginMap.empty
    (*module Gamma = Map.Make(String)*)
    type theta = Oratio.ratio 

    type treatment = cpo_expr Delta.t * theta * Phi.t
    type cond_set = cpo_expr Sigma.t * Phi.t 
    type semantic_tuple = (treatment list) * cond_set
    type typequals = Cpo.typequals
    type graph = Cpo.graph

    (*  Helpers/intermediate structs *)
    module PHelp = struct 
      include Set.Make(struct
          type t = Config.ssa_id option * inlang_expr
          let compare (p1:t) (p2:t) = if p1 = p2 then 0 else -1 
        end)
      let has_key k phelp = 
        elements phelp
        |> List.exists (fun (a, _) -> match a with 
            | Some k' when k' = k -> true 
            | _ -> false)
      let get_expr k phelp = 
        elements phelp 
        |> List.find (fun (a, _) -> match a with 
            | Some k' when k' = k -> true 
            | _ -> false)
        |> snd 
      let remove_key phelp (k : Config.ssa_id) = 
        if has_key k phelp
        then begin 
          List.fold_left (fun phelp (k', v) -> match k' with 
            | Some s when s = k -> phelp
            | _ -> add (k', v) phelp)
            empty (elements phelp)
        end else phelp
      let remove_name phelp (k : Config.ssa_id) =
        let name = Cpo.get_delta_key k in 
        List.fold_left (fun phelp tupe -> match fst tupe with 
          | Some s -> 
            let name' = Cpo.get_delta_key s in 
            if name' = name 
            then phelp
            else add tupe phelp
          | None -> add tupe phelp 
          ) empty (elements phelp)
      let bindings phelp = 
        elements phelp
        |> Utils.filter_map (fun (optkey, expr) -> match optkey with 
            | Some k -> Some (k, expr)
            | _ -> None)
      let merge phelp1 phelp2 = 
        elements phelp1 @ (elements phelp2)
        |> List.fold_left (fun phelp (k, v) -> 
            match k with 
            | None -> add (k, v) phelp
            | Some k' when not (has_key k' phelp) || (get_expr k' phelp) = v
              -> add (k, v) phelp
            | _ -> assert false) empty
      end
    type tmt = cpo_expr Ctxt.t * theta * PHelp.t 
    type cndst = cpo_expr Ctxt.t * PHelp.t
    module Avoid = Set.Make(String)
    module Declared = Set.Make(String)

    module Format = struct 
      open Sexplib.Conv
      open Printf 
      
      let string_of_id = Config.string_of_ssa_id
      let string_of_inlang_expr = Cpo.string_of_cpo_expr

      let string_of_delta delta = 
          sprintf "\n {\n\t%s\n }" 
          (Utils.join "\n\t" (fun (k, v) -> 
              sprintf "%s : %s" k
                  (string_of_cpo_expr v))
              (Delta.bindings delta)) 
      
      let string_of_phi phi = 
        (Utils.join "\n\t" string_of_cpo_expr (Phi.elements phi))

      let string_of_cond_set (cond_set, phis) = 
        sprintf "{%s}%s"
          (Utils.join "; " (fun (k,v) -> Printf.sprintf "%s : %s" k
            (string_of_cpo_expr v)) 
            (Sigma.bindings cond_set))
          (if Phi.cardinal phis = 0 then "" else " with\n\t" ^ (string_of_phi phis))

      let string_of_treatment (treatment : treatment) = 
          let (e, t, phi) = treatment in 
          sprintf "%s : %s%s" 
            (string_of_delta e) 
            (Oratio.string_of_ratio t) 
            (if Phi.cardinal phi = 0 then "" else " with\n\t" ^ (string_of_phi phi))

      let string_of_semantics_tuples (sem_list : semantic_tuple list) = 
          let string_of_semantic_tuple (sem_tuple : semantic_tuple) : string =
              let ((dt_list : treatment list), cond_set) = sem_tuple in 
              (string_of_cond_set cond_set) ^ 
              (Utils.join "\n  " string_of_treatment dt_list) in 
          Utils.join "\n====================================\n"
            string_of_semantic_tuple sem_list

      let rec string_of_prop = function 
        | Not b -> sprintf "!%s" (string_of_prop b) 
        | And (b1, b2) ->
          sprintf "(%s && %s)"
            (string_of_prop b1)
            (string_of_prop b2)
        | Or (b1, b2) ->
          sprintf "(%s || %s)"
            (string_of_prop b1)
            (string_of_prop b2) 
        | Id id -> string_of_id id
        | True -> "true"
        | False -> "false"
  
      let string_of_randomness r = match r with 
        | Config.Det 
        | Config.Rand _ -> Config.sexp_of_randomness r |> Sexplib.Sexp.to_string 
        | Config.CS {rands; dets} -> 
          Printf.sprintf "CS {rands={%s}; dets=[%s]}"
            (Utils.join "; " (fun (i, lst) -> 
              Printf.sprintf "%d=>[%s]" i (Utils.join ";" Utils.identity lst))
              rands)
            (Utils.join "; " string_of_int dets)
      
      let string_of_qualifier {card; dyn; rand; corr} : string =
          sprintf "<%s, %s, %s, %s>"
              (Config.sexp_of_cardinality card |> Sexplib.Sexp.to_string)
              (Config.sexp_of_dynamism dyn |> Sexplib.Sexp.to_string)
              (string_of_randomness rand)
              (Config.sexp_of_corr_t corr |> Sexplib.Sexp.to_string)

      let rec string_of_node = function 
          | Assign (_, k, qs, e) -> 
            sprintf "%s %s=%s;"
              (string_of_qualifier qs)
              (string_of_id k)
              (string_of_cpo_expr e)
          | Assert p -> Printf.sprintf "assert %s;" (string_of_prop p)
          | Declare (k, qs, t) ->
            sprintf "declare %s %s %s;" 
              (string_of_qualifier qs)
              (match t with Some t -> Smtlib.string_of_sort t | _ -> "??")
              (string_of_id k)
          | Return p -> Printf.sprintf "return %s;" (string_of_prop p)
      and string_of_path p =
          Utils.join "\n" string_of_node p 
          (*List.fold_left (fun s p -> s ^ string_of_node p ^ " ") "\n" p  *)
      and string_of_program (p : program) = 
          Utils.join "\n\n" string_of_path p 
          (*List.fold_left (fun s p -> s ^ string_of_path p) "\n\n" p  *)

      let ast_string_of_id k = Cpo.ast_string_of_id k

      let ast_string_of_tq {card; dyn; rand; corr} = 
        let str_wrap s = sprintf "\"%s\"" s in 
        sprintf "{card=%s; dyn=%s; rand=%s; corr=%s}" 
          (Config.sexp_of_cardinality card |> Sexplib.Sexp.to_string)
          (Config.sexp_of_dynamism dyn |> Sexplib.Sexp.to_string)
          (match rand with
           | Config.Det -> "Det"
           | Config.Rand slist -> 
             sprintf "Rand [%s]" (Utils.join "; " str_wrap slist)
           | Config.CS {dets; rands} ->
             sprintf "CS <opaque>")
          (Config.sexp_of_corr_t corr |> Sexplib.Sexp.to_string)
      
      let ast_string_of_origin o = Config.show_origin o |> sprintf "%s"

      let ast_string_of_inlang e = Cpo.ast_string_of_inlang_expr e

      let rec ast_string_of_prop = function 
        | True -> "True" 
        | False -> "False"
        | Id k -> sprintf "Id %s" (ast_string_of_id k)
        | Not p -> sprintf "Not (%s)" (ast_string_of_prop p)
        | And (p1, p2) -> sprintf "And (%s, %s)" 
          (ast_string_of_prop p1)
          (ast_string_of_prop p2)
        | Or (p1, p2) -> sprintf "Or (%s, %s)"
          (ast_string_of_prop p1)
          (ast_string_of_prop p2)

      let ast_string_of_node = function 
        | Declare (k, tq, t) -> sprintf "Declare (%s, %s, %s)"
          (ast_string_of_id k) 
          (ast_string_of_tq tq) 
          (match t with 
          | Some s -> sprintf "Some (%s)" (Smtlib.ast_string_of_sort s)
          | _ -> "None")
        | Assign (o, k, tq, e) -> sprintf "Assign (%s, %s, %s, %s)"
          (ast_string_of_origin o) 
          (ast_string_of_id k)
          (ast_string_of_tq tq)
          (ast_string_of_inlang e)
        | Assert p -> sprintf "Assert (%s)"
          (ast_string_of_prop p)
        | Return p -> sprintf "Return (%s)"
          (ast_string_of_prop p)

      let ast_string_of_path path = 
        Utils.join "; " ast_string_of_node path 
        |> sprintf "[%s]"

      let ast_string_of_program (program : pi list) = 
        Utils.join "\t\n" ast_string_of_path program 
        |> sprintf "[\n\t%s\n]"

      let ast_string_of_cond_set ((cset, phi) : cond_set) = 
        let cset_string = sprintf "Sigma.empty %s"
          (Utils.join "" (fun (k, v) -> 
            let v' = Cpo.ast_string_of_inlang_expr v in 
            sprintf "|> Sigma.add \"%s\" (%s)" k v')
           (Sigma.bindings cset)
          ) in
        let phi_string = sprintf "Phi.empty %s"
          (Utils.join "" (fun e -> 
            sprintf "|> Phi.add (%s)" (Cpo.ast_string_of_inlang_expr e))
           (Phi.elements phi)
          ) in  
        Printf.sprintf "(%s, %s)" cset_string phi_string 

      end 

    module SMT = Smtlib.Make(struct 
        type cpo_expr = Cpo.cpo_expr 
        type basetype = Cpo.basetype 
        let mock = Cpo.mock
        let id_of_base_type = Cpo.id_of_base_type
        let exp_to_term = Cpo.expr_to_term 
      end)

    (* let solver = ref (SMT.make_solver Cpo.smt) *)

    let toggle_mock () = SMT.check_mock true 
      
    module DataStructOps = struct 
      (* convert to the appropriate final key *)
      let delta_key_from_node n = match n with 
        | Declare (k, _, _)
        | Assign (_, k, _, _) -> Some (Cpo.get_delta_key k)
        | _ -> None 
  
      let merge_delta_sigma_phi ctxt sigma phi =
        (* We don't export Map.merge in Delta's signature, and we would need to 
        enforce type constraints between Delta and Sigma. Instead just add them. 
        This function doesn't get used outside this module anyway. *)
        List.fold_left (fun d (k, v) -> Ctxt.add k v d) 
          ctxt (Ctxt.bindings sigma @ (PHelp.bindings phi))
  
    end 

    module NodeQueries = struct 
      let is_random (node : node) : bool = 
        match node with 
        | Assign (_, _, {rand}, _) 
        | Declare (_, {rand}, _) -> 
          begin match rand with 
            | Config.Rand _ -> true 
            | _ -> false 
          end 
        | _ -> false 
  
    end 

    module PathQueries = struct 
      let path_has_randomness (p : pi) : bool = 
        Utils.exists NodeQueries.is_random p 

      let is_path_logged (p : pi) : bool = 
        (* eval_return will return an empty list if the path is not logged. *)
        let match_return n = match n with Return _ -> true | _ -> false in 
        if List.exists match_return p 
        then match List.find match_return p with 
          | Return True -> true 
          | Return False -> false 
          | _ -> assert false 
        else true  

      let get_expr_for_assign (s : Config.ssa_id) (ps: pi list) = 
        let rec helper = function 
        | [] -> None
        | (Assign (_, s', _, e))::t when s = s' -> Some e
        | _::t -> helper t in 
        let exprs = Utils.filter_map helper ps in 
        (* This assert will fail for paths that have duplicated heads. *)
        (* assert (List.length exprs = 1); *)
        List.hd exprs
    end 
    
    module SMTAux = struct
      module Logger = Logging.Make (struct 
          let file = __FILE__
          let phase = Logging.Semantics 
        end)

      let function_id (Smtlib.Id s, _) = 
        try
          ignore (Config.ssa_id_of_string s); false
        with 
        | Failure msg when msg = "int_of_string" -> true

      let declare_and_add_if_not_declared solver declared id t : unit = 
        let k = Config.string_of_ssa_id id in 
        if (not (Declared.mem k !declared)) &&
            (SMT.declare_const solver (Cpo.identifier_of_ssa_id id) t) 
        then declared := Declared.add k !declared

      let push_cond_set solver declared s = 
        (* Conditioning set elements are all final. *)
        List.iter (fun (k, v) -> 
          declare_and_add_if_not_declared solver declared k (Cpo.get_expr_type v 
                                                      |> Cpo.id_of_base_type);
          SMT.assert_ solver (Cpo.expr_to_term v)
        ) (Ctxt.bindings s)
  
      let push_treatment declared tmt = 
        (* List.iter (fun (k, v)) *)
        ()
  
      let push_phi declared phi = 
        List.iter (fun e -> 
        (* every expression in the conditioning set is boolean *)
        ()
        ) (PHelp.elements phi)    
      
      let rec pred_to_term pred = 
        match pred with 
        | True -> Smtlib.bool_to_term true 
        | False -> Smtlib.bool_to_term false 
        | Id k -> Smtlib.const (Config.string_of_ssa_id k)
        | Not p -> Smtlib.not_ (pred_to_term p)
        | And (p1, p2) -> Smtlib.and_ (pred_to_term p1) 
                                      (pred_to_term p2)
        | Or (p1, p2) -> Smtlib.or_ (pred_to_term p1) 
                                    (pred_to_term p2)
      let pred_to_inlang_expr pred = 
        let rec to_term pred = match pred with 
          | True -> Smtlib.bool_to_term true 
          | False -> Smtlib.bool_to_term false 
          | Id k -> Smtlib.const (Config.string_of_ssa_id k)
          | Not p -> Smtlib.not_ (to_term p)
          | And (p1, p2) -> Smtlib.and_ (to_term p1) (to_term p2)
          | Or (p1, p2) -> Smtlib.or_ (to_term p1) (to_term p2) in 
        to_term pred |> Cpo.term_to_expr

      let print_bindings line str bindings = 
        Logger.print_debug line "%s bindings:\n\t%s\n" 
          str
          (Utils.join "\n\t" (fun (k, v) -> 
            Printf.sprintf "%s : %s" 
              (Config.string_of_ssa_id k) 
              (Cpo.string_of_cpo_expr v)) 
           bindings)


      (* Declares all the types and expression, functions, relations, etc. 
        for the input conditioning set, treatment environment, and phi sets. *)
      let push_context solver declared s dt phi : unit = 
        (* First declare the types of all the variables. *)
        print_bindings __LINE__ "unevaled" (PHelp.bindings phi);
        print_bindings __LINE__ "conset" (Ctxt.bindings s);
        print_bindings __LINE__ "treatments" (Ctxt.bindings dt);
        let bindings = [PHelp.bindings phi; Ctxt.bindings s; Ctxt.bindings dt]
          |> List.fold_left (@) []
          |> Utils.uniq in 
        for i=0 to List.length bindings - 1 do 
          let (id, e) = List.nth bindings i in 
          let t = Cpo.get_expr_type e |> Cpo.id_of_base_type in 
          declare_and_add_if_not_declared solver declared id t;
          let vars = Cpo.get_expr_vars e in 
          for j=0 to List.length vars - 1 do 
            let v = List.nth vars j in 
            let t = Cpo.get_expr_type ~var:(Some v) e |> Cpo.id_of_base_type in 
            declare_and_add_if_not_declared solver declared v t
          done 
        done

      let get_pred_assignment solver pred_term = 
        let term_string = Smtlib.string_of_term pred_term in 
        Logger.print_debug __LINE__ "Asserting predicate: %s" term_string;
        SMT.assert_ solver pred_term;
        match SMT.check_sat solver with 
        | SMT.Unsat -> 
          Logger.print_debug __LINE__ "%s is unsat" term_string;
          None 
        | SMT.Unknown -> assert false (* Dunno what this means *)
        | SMT.Sat -> Some (SMT.get_model solver)

      let negate_term pred_term = Smtlib.not_ pred_term
        
      (* Loops through the assignments in pred_model and sets the concrete 
         terms in either the treatment environment (dt) or the conditioning set 
         (s). *)
      let set_guard_assertions pred_model dt s sphi = 
        List.fold_left (fun (dt, s) (Smtlib.Id id, term) -> 
            let k = Config.ssa_id_of_string id in 
            let v = Cpo.term_to_expr term in 
            let env = DataStructOps.merge_delta_sigma_phi dt s sphi in 
            (* if Ctxt.mem k s 
            then (assert (Ctxt.find k s = v); dt, s)
            else  *)
            if Cpo.condition_on v env || PHelp.has_key k sphi || Ctxt.mem k s
            then (dt, Ctxt.add k v s)
            else (Ctxt.add k v dt, s)
          )
          (dt, s) pred_model

      (* Loops through the assignments in pred_model and assert the definitions
         upstream from the values being set. So, if a program is defined like 
         so:
            asdf = (a * b) % 3;
            foo = asdf == 1 || asdf == 2;
            if (foo) { ... } 
         then we will have declared a, b, and asdf as integers, and foo as a 
         boolean to the smt !solver, and when we assert that foo is true, we will 
         get back a model that looks something like this:
             [(asdf, 1); (a, 1); (b, 1)]
          *)
      let pred_assert_references solver avoid s sphis dt dtphis dt_temp pred_model = 
        let module Asserted = Set.Make(String) in 
        let asserted = ref Asserted.empty in 
        let sat = ref SMT.Unknown in 
        for i=0 to List.length pred_model - 1 do 
          let (Smtlib.Id id, term) = List.nth pred_model i in 
          let k1 = Config.ssa_id_of_string id in 
          let v1 = Cpo.term_to_expr term in 
          Logger.print_debug __LINE__
            "k1 : %s\n\tin treatment? : %b\tin treatment phis? %b
            \n\tin conditioning set? : %b\tin condset phis? %b\n" 
            (Config.string_of_ssa_id k1) 
            (Ctxt.mem k1 dt) 
            (PHelp.has_key k1 dtphis)
            (Ctxt.mem k1 s)
            (PHelp.has_key k1 sphis);
          (* If key is already in dt or s and is final, make sure it's 
             consistent with the assignment. *)
          let previously_concretized env = 
            if Ctxt.mem k1 env
            then 
              let v = Ctxt.find k1 env in 
              Logger.print_debug __LINE__ "%s: %s vs. %s"
                (Config.string_of_ssa_id k1)
                (Cpo.string_of_cpo_expr v) 
                (Cpo.string_of_cpo_expr v1);
              Some (v = v1)
            else None in 
          match previously_concretized dt, previously_concretized s with 
            | Some true, None 
            | None, Some true -> 
              Logger.print_debug __LINE__ 
                "Value has already been set and reasoned about.";
              sat := SMT.Sat 
            | Some false, None 
            | None, Some false -> 
              Logger.print_debug __LINE__ 
                "Value has already been set and is inconsistent.";
              sat := SMT.Unsat
            | Some _, Some _ -> 
              Logger.print_debug __LINE__
                "%s in both treatment and conditioning set" id;
              assert false 
            | None, None -> 
              if PHelp.has_key k1 (PHelp.union sphis dtphis)
              then 
                (* Concretize this variable and assert its references. *)
                let used = ref [k1] in
                while List.length !used <> 0 do
                  let k2 = List.hd !used in 
                  let phis = PHelp.union sphis dtphis in 
                  if PHelp.has_key k2 phis 
                  then 
                    let e = PHelp.get_expr k2 phis in 
                    if Cpo.is_opaque e 
                    then used := [] 
                    else if Cpo.is_pred e
                    then begin
                      let new_pred_term = Cpo.expr_to_term (match term with 
                        | Smtlib.Const (Smtlib.Id "true") -> e
                        | Smtlib.Const (Smtlib.Id "false") -> Cpo.negate_expr e
                        | _ -> assert false) in  
                      let vars_used = Cpo.get_expr_vars e in 
                      let no_holes = vars_used
                        |> List.map Config.string_of_ssa_id
                        |> List.for_all (fun s -> not (Avoid.mem s avoid)) in 
                      Logger.print_debug 
                        __LINE__
                        "k2: %s = %s\nAssrting new_pred_term (%s)? %b\n" 
                        (Config.string_of_ssa_id k2) 
                        (Cpo.string_of_cpo_expr e) 
                        (Smtlib.string_of_term new_pred_term) 
                        no_holes; 
                      if no_holes then SMT.assert_ solver new_pred_term;
                      asserted := Asserted.add id !asserted;
                      used := List.tl !used @ (
                        vars_used
                        |> List.filter (fun k -> 
                          let k = Config.string_of_ssa_id k in 
                          not (Asserted.mem k !asserted) && 
                          (not (Avoid.mem k avoid))))
                      end 
                    else used := List.tl !used; 
                  else used := List.tl !used; 
                done;
              else ()
        done;
        (* Solver logic *)
        if (!sat <> SMT.Unsat) && (SMT.check_sat solver = SMT.Sat)
        then 
          let values = SMT.get_model solver 
            |> List.filter (Utils.not_fn function_id) in 
          Logger.print_debug __LINE__ "values: %s\n" 
            (Utils.join "\n" 
              (fun (Smtlib.Id id, term) -> 
                Printf.sprintf "%s : %s" id (Smtlib.term_to_string term)) 
              values);
          let (dt', dtphis', s', sphi') = 
            List.fold_left (fun (dt, dtphis, s, sphis) 
                                (Smtlib.Id id', term) ->
                let id = Config.ssa_id_of_string id' in 
                let e = Cpo.term_to_expr term in 
                let env = DataStructOps.merge_delta_sigma_phi 
                  dt s (PHelp.union dtphis sphis) in 
                let is_final = Cpo.is_final e in 
                let is_treatment = Ctxt.mem id dt || PHelp.has_key id dtphis in
                let is_condition = Ctxt.mem id s || PHelp.has_key id sphis in 
                let condition_on =  Cpo.condition_on e env in 
                Logger.print_debug __LINE__ 
                  "id: %s\te : %s\tis_final: %b\tcondition_on: %b\ttreatment: %b\tcondition: %b" 
                  id'
                  (Cpo.string_of_cpo_expr e)
                  is_final condition_on is_treatment is_condition;
                if is_final && is_treatment 
                then (Ctxt.add id e dt, PHelp.remove_key dtphis id, s, sphis)
                else if is_final && is_condition
                then (dt, dtphis, Ctxt.add id e s, PHelp.remove_key sphis id)
                  (* else assert false  *)
                else if condition_on || is_condition
                then (dt, dtphis, s, PHelp.add (Some id, e) sphis)
                else (dt, PHelp.add (Some id, e) dtphis, s, sphis)
              )
              (* (dt_temp, dtphis, s, sphis)  *)
              (dt, dtphis, s, sphis)
              values in 
          Some (dt', dtphis', s', sphi', values)
          else None 
    end
      
    module Logger = Logging.Make(struct 
        let file = __FILE__
        let phase = Logging.Semantics
      end)

    let raise_units_low_cardinality cfg n path : unit =
      match n with 
      | Assign (_, _, {rand}, _) -> 
        (* Printf.printf "Node: %s" (Format.string_of_node n); *)
        (* We need at least one unit with high cardinality. *)
        begin match rand with 
          | Config.Rand units -> 
            assert (List.length units > 0);
            let high_card = List.find_all (fun unit_string -> 
              (* print_string (Cpo.POCfg.string_of_typequals cfg); *)
              Cpo.POCfg.get_cardinality unit_string cfg = Some Config.High)
              units in 
            if List.length high_card = 0 
            then raise (Static_errors.UnitLowCardinality (List.hd units))
            else ()
          | _ -> ()
        end
      | _ -> ()

    let finalize_treatments dtlist = 
      dtlist 

    let finalize_conditioning_sets s sphi = (s, sphi)

    let move_finals d p = 
      let to_move = PHelp.bindings p 
        (* First evaluate all of the k-v pairs. *)
        |> List.map (fun (k, v) -> (k, Cpo.eval_cpo_expr d v))
        (* Remove anything that isn't final. *)
        |> List.filter (fun (_, v) -> Cpo.is_final v) in
      (* Return a tuple that adds the k-v pairs to the treatment 
          and removes the keys from the phis. *)           
      (List.fold_left (fun env (k, v) -> Ctxt.add k v env) d to_move,
       List.fold_left (fun phi (k, _) -> PHelp.remove_key phi k) p to_move)
  

    let negate_val (id, term) = Smtlib.not_ (Smtlib.equals (Smtlib.Const id) term)

    let unique_solution solver (val_terms : (Smtlib.identifier * Smtlib.term) list) : bool = 
      let uniq = ref true in 
      SMT.push solver;
      for i=0 to List.length val_terms - 1 do
        let val_term = List.nth val_terms i in 
        SMT.push solver;
        SMT.assert_ solver (negate_val val_term);
        begin match SMT.check_sat solver with 
          | SMT.Sat -> uniq := false
          | SMT.Unknown -> assert false
          | SMT.Unsat -> ()
        end;
        SMT.pop solver;
      done;
      SMT.pop solver;
      !uniq

    let string_of_ctxt ctxt = 
      Ctxt.bindings ctxt
      |> Utils.join "; " (fun (k, v) -> Printf.sprintf "%s => %s" 
            (Config.string_of_ssa_id k) 
            (Cpo.string_of_cpo_expr v))
      |> Printf.sprintf "{%s}" 

    let string_of_phelp phelp = 
      PHelp.elements phelp
      |> Utils.join "\n\t" (fun (k, v) -> match k with 
         | None -> Cpo.string_of_cpo_expr v
         | Some s -> Printf.sprintf "%s == %s" (Config.string_of_ssa_id s) (Cpo.string_of_cpo_expr v))
      |> Printf.sprintf "Phi: %s"
      
    let update_avoid (avoid: Avoid.t ref) (k : string) : unit = 
      Logger.print_debug __LINE__ "Adding %s to the avoid list (%s)"
        k (Utils.join ", " Utils.identity (Avoid.elements !avoid));
      avoid := Avoid.add k !avoid 

    let update_declared (declared : Declared.t ref) (k : string) : unit = 
      declared := Declared.add k !declared

    let eval_assert solver (avoid : Avoid.t) declared path pred s phis treatment  
     : (tmt list * cndst) option = 
      Logger.print_debug __LINE__ "Evaluating assert %s" 
        (Format.string_of_prop pred);
      SMT.push solver;
      let (dt, r, dt_phis) = treatment in
      SMTAux.push_context solver declared s dt (PHelp.union phis dt_phis);
      let pred_term = ref (SMTAux.pred_to_term pred) in 
      let continue  = ref true in 
      let tr_list   = ref [] in 
      let cset      = ref s in 
      let sphis     = ref phis in 
      while !continue do 
        match SMTAux.get_pred_assignment solver !pred_term with 
        | None -> continue := false 
        | Some pred_model -> 
          Logger.print_debug __LINE__ "predicate model: [%s]"
            (Utils.join "; " (fun (Smtlib.Id k, v) -> 
                Printf.sprintf "%s => %s" k (Smtlib.term_to_string v))
              pred_model);
          let dt_temp, cset_temp = 
            SMTAux.set_guard_assertions pred_model dt !cset !sphis in 
          let post_assertion = 
            SMTAux.pred_assert_references solver avoid !cset !sphis dt dt_phis dt_temp 
              pred_model in 
          begin match post_assertion with 
            | Some (dt_temp', dtphis', s', sphis', new_pred_terms) -> 
              Logger.print_debug __LINE__
                ("\n  dt_temp old: %s\n  dt_temp new: %s" ^^
                 "\n  s old: %s\n  s new: %s" ^^
                 "\n  dtphis old: %s\n  dtphis new: %s" ^^
                 "\n  sphis old: %s\n  sphis new: %s" ^^
                 "\n  new_pred_terms: %s")
                (string_of_ctxt dt_temp) (string_of_ctxt dt_temp') 
                (string_of_ctxt cset_temp) (string_of_ctxt s') 
                (string_of_phelp dt_phis) (string_of_phelp dtphis') 
                (string_of_phelp phis) (string_of_phelp sphis')
                (Utils.join "\n\t" (fun (Smtlib.Id id, term) -> 
                  Printf.sprintf "%s : %s" id (Smtlib.string_of_term term)) 
                 new_pred_terms);
              if unique_solution solver new_pred_terms 
              then begin
                Logger.print_debug __LINE__ "Unique solution.";
                (* just changed from old dtphis to returned dtphis -- not sure 
                   if this is a mistake or if i was doing it for a reason. *)
                tr_list := (dt_temp', dtphis')::!tr_list; 
                cset := s';
                sphis := sphis' end
              else begin 
                (* if it's an assertion about a treatment, add it to the 
                   treatment phis. o/w add it to the conditioning phis. *)
                Logger.print_debug __LINE__ "Not a unique solution.";
                tr_list := (move_finals dt_temp dt_phis)::!tr_list
                (* how are dt phis getting into sphis? commenting the line below
                fixes the problem and im not sure why. *)
                (* sphis := PHelp.add (None, SMTAux.pred_to_inlang_expr pred
                                          |> Cpo.replace_gets !cset) !sphis *)
                  (* might need to do something here with csets, phis*)
              end 
            | None -> ()
          end;
          pred_term := SMTAux.negate_term !pred_term;
      done;
      SMT.pop solver;
      Some (List.map (fun (tr, dt_phis) -> 
        (tr, r, dt_phis)) !tr_list, (!cset, !sphis))

    let generate_treatments cfg s e k cphis dt_list_new (d, t, tphis) = 
      let env = 
        DataStructOps.merge_delta_sigma_phi d s (PHelp.merge cphis tphis) in 
      let e = Cpo.eval_cpo_expr env e in 
      let worlds = Cpo.randomly_split_worlds cfg e in
      let num_worlds = List.length worlds in 
      if num_worlds > !Cpo.max_choices 
      then raise (Exceptions.ToolFailures.TooManyChoices 
        (fst k, List.length worlds));
      List.map (fun (v, r) ->
        let v' = Cpo.eval_cpo_expr env v in 
        (* This is so that, once we have a -1, we don't change it. *)
        let r' = if Oratio.lt r Oratio.zero then r else Oratio.multiply t r in 
        if Oratio.equals r' Oratio.zero 
        then raise (Static_errors.PositivityError (Cpo.get_delta_key k, v'));
        if Cpo.is_final v'
        then 
          let (d', tphis') = (* (d, tphis) in *)
            move_finals (Ctxt.add k v' d) (PHelp.remove_key tphis k) in  
          (d', r', tphis')
        else (d, Oratio.neg_one, PHelp.add (Some k, v') tphis)
      ) worlds @ dt_list_new

    let eval_assign solver declared cfg path dt_list o n s cphis k q e = 
      (* Track var origin so we can remove synthetic ones later. *)
      origin_map := OriginMap.add k o !origin_map;
      (* Declare variables in z3. *)
      SMTAux.declare_and_add_if_not_declared solver declared k 
        (Cpo.get_expr_type e |> Cpo.id_of_base_type); 
      (* Add to the semantic tuples. *)
      let rand = NodeQueries.is_random n in 
      let final = Cpo.is_final e in 
      let opaque = Cpo.is_opaque e in 
      Logger.print_debug __LINE__
        "Evaluating %s\n\tis random: %b\n\tis final: %b\n\tis opaque: %b"
        (Format.string_of_node n) rand final opaque;
      (* if not (Cpo.is_opaque e)
      then SMT.assert_ !solver (Cpo.expr_to_term e); *)
      (* Printf.printf "%s\n" msg; *)
      if rand
      then begin
        (* If the variable is random, then it is a potential treatment. *)
        raise_units_low_cardinality cfg n path;
        let new_treatments = 
          List.fold_left (generate_treatments cfg s e k cphis) [] dt_list in 
        [new_treatments, (s, cphis)] 
        end 
      else if final
      (* then [dt_list, (Ctxt.add k e s, PHelp.remove_key cphis k)] *)
      then [List.map (fun (d, r, p) -> 
              (Ctxt.add k e d, r, PHelp.remove_key p k))
            dt_list, (s, PHelp.remove_key cphis k)]
      (* else if opaque  *)
      else [dt_list, (s, PHelp.add (Some k, e) cphis)]
      (* else begin 
          SMT.assert_ !solver (Smtlib.Const (Cpo.identifier_of_ssa_id k));
          (* SMT.assert_ !solver (Cpo.expr_to_term e); *)
          let tr = Smtlib.bool_to_term true |> Cpo.term_to_expr in 
          [dt_list, (Ctxt.add k tr s, PHelp.remove_key cphis k)]
      end  *)

    let eval_return path dt_list s phis e = 
      match e with 
      | True -> [dt_list, (s, phis)]
      | False -> []
      | _ -> assert false 

    (* Each time we evaluate a node, we can generate multiple worlds. *)
    let eval_node solver (avoid : Avoid.t ref) declared cfg path dt_list s phis n =
      match n with 
      | Assign (o, k, q, e) -> 
        (* Assignment causes branching through multiple treatment values. *)
        eval_assign solver declared cfg path dt_list o n s phis k q e
      | Assert p -> 
        (* Assertion causes branching through multiple conditioning sets. 
           Assertions may be unsatisfiable, so we filter only the SAT ones. *)
        Utils.filter_map (eval_assert solver !avoid declared path p s phis) dt_list
      | Declare (k, qs, t) -> 
        (* Register declared variables. *)
        origin_map := OriginMap.add k Config.ExtSource !origin_map;
        let id = Cpo.identifier_of_ssa_id k in 
        if SMT.declare_const solver id t
        then update_declared declared (Config.string_of_ssa_id k)
        else update_avoid avoid (Config.string_of_ssa_id k);
        (* No changes to the output. *)
        [dt_list, (s, phis)]
      | Return e -> 
        (* Filters unlogged data. *)
        eval_return path dt_list s phis e

    let eval_path solver cfg (p : pi) : ((tmt list) * cndst) list =
      SMT.push solver;
      (* There are some variables whose types we don't know -- we need to avoid 
         sending information about them to the smt !solver. *)
      let avoid = ref Avoid.empty in 
      (* Track all of the declared variables, since z3 barfs when you try to 
         declare a variable twice! *)
      let declared = ref Declared.empty in 
      (* Evaluate each node to get all of the possible worlds. *)
      let evaled = List.fold_left (fun tupe_list (n : node) -> 
        (* Each node could have multiple worlds. Worlds can split on treatment 
        or conditioning set. Every new node causes every old node to branch. *)
          List.map (fun (dt_list, (s, phis)) ->
            eval_node solver avoid declared cfg p dt_list s phis n) tupe_list
          |> List.flatten)
        [[Ctxt.empty, Oratio.one, PHelp.empty], (Ctxt.empty, PHelp.empty)]
        p in 
      SMT.pop solver;
      Utils.filter_map (fun (dtlist, s) -> 
        let dtlist' = List.filter (fun (d, _, _) -> 
           Ctxt.cardinal d > 0) dtlist in 
        if List.length dtlist > 0 && List.length dtlist' > 0 
        then Some (dtlist', s)
        else None)
      evaled 

    let conditioned_on_eq (tupe1 : semantic_tuple) (tupe2 : semantic_tuple) = 
      let (_, (s1, sphi1)) = tupe1 in 
      let (_, (s2, sphi2)) = tupe2 in 
      Sigma.equal (=) s1 s2 && Phi.equal sphi1 sphi2

    let rec merge_equivalent_conditioning_sets : semantic_tuple list -> 
      semantic_tuple list = function
      | [] -> []
      | head::tail ->  
        let (s_same, s_diff) = List.partition (conditioned_on_eq head) tail in 
        let treatments = List.fold_left (@) (fst head) (List.map fst s_same) in 
         (treatments, snd head)::
          (merge_equivalent_conditioning_sets s_diff)

    let filter_synthetic_vars_ctxt (dt : inlang_expr Ctxt.t) : inlang_expr Ctxt.t = 
      Ctxt.bindings dt
      |> List.fold_left (fun dt (k, v) -> 
        if OriginMap.mem k !origin_map 
        then if OriginMap.find k !origin_map = Config.Source
        then Ctxt.add k v dt
        else dt
        else failwith 
          (Printf.sprintf "%s not in origin map" (Config.string_of_ssa_id k))) 
        Ctxt.empty
    
    let filter_synthetic_vars_phelp phelp =
      PHelp.elements phelp
      |> List.fold_left (fun phelp (id, e) -> 
          match id with 
          | Some k -> 
            if OriginMap.find k !origin_map = Config.Synth
            then PHelp.remove_key phelp k
            else phelp
          | None -> phelp
        ) phelp

    let filter_synthetic_vars tupes = 
      List.map (fun (dt_list, (s, s_phi)) -> 
        (List.map (fun (dt, r, t_phi) -> 
          (filter_synthetic_vars_ctxt dt, 
           r, 
           filter_synthetic_vars_phelp t_phi)) dt_list,
         (filter_synthetic_vars_ctxt s, 
          filter_synthetic_vars_phelp s_phi)))
      tupes 

    let convert_varidkeys l : semantic_tuple list = 
      let convert_to_delta ctxt : cpo_expr Delta.t = 
        List.fold_left (fun dt (k, _) ->
          Delta.add (Cpo.get_delta_key k) 
                    (Cpo.get_final_binding k ctxt)
                    dt)
          Delta.empty 
          (Ctxt.bindings ctxt) in
      let convert_to_sigma ctxt : cpo_expr Sigma.t = 
        List.fold_left (fun dt (k, _) ->
          Sigma.add (Cpo.get_delta_key k)
                    (Cpo.get_final_binding k ctxt)
                    dt)
          Sigma.empty
          (Ctxt.bindings ctxt) in  
      let convert_to_phi phelp = 
        List.fold_left (fun p (a, b) -> 
            match a with 
            | Some k -> Phi.add (Cpo.to_eq_rel k b) p
            | None -> Phi.add b p)
          Phi.empty (PHelp.elements phelp)
         in 
      let convert_to_treatment (ctxt, r, phelp) = 
        (convert_to_delta ctxt, r, convert_to_phi phelp) in 
      let convert_to_cond_set s p = 
        (convert_to_sigma s, convert_to_phi p) in 
      let convert_to_semantic_tuple (tupe : (tmt list) * cndst) : semantic_tuple = 
        let (dt_list, (s, p)) = tupe in 
        (List.map convert_to_treatment dt_list, convert_to_cond_set s p) in 
      List.map convert_to_semantic_tuple l

    let rec declare_functions solver p = 
      let module Declared = Set.Make(struct 
        type t = Smtlib.identifier 
        let compare t1 t2 = if t1 = t2 then 0 else -1 end) in 
      let declared = ref Declared.empty in 
      List.iter (fun (path : pi) -> 
        List.iter (fun (n : node) -> match n with 
          | Assign (_, _, _, e) -> 
            begin match Cpo.external_function e with 
              | Some (name, args_types, return_type) 
                when not (Declared.mem name !declared) ->
                  (*SMT.declare_fn !solver name args_types return_type;*)
                  ignore (SMT.declare_const solver name (Some return_type));
                  declared := Declared.add name !declared 
              | _ -> ()
            end
          | _ -> ())
          path) 
        p

    let remove_constants constants tupes = 
      Logger.print_debug __LINE__ "Constants: [%s]" 
        (Utils.join "; " Utils.identity constants);
      List.map (fun ((treatment_list : treatment list), other) -> 
        (List.map (fun (dt, a, b) -> 
          (List.fold_left (fun dt k -> Delta.remove k dt) dt constants, a, b)
          ) treatment_list, other)
      ) tupes 
      

    let remove_non_dependents_from_conditioning_sets ddg tupes = 
      List.map (fun ((treatment_list : tmt list), (s, phis)) ->
        let all_treatment_variables = List.map (fun (t, _, _) ->
            Ctxt.bindings t |> List.map fst
          ) treatment_list |> List.flatten in 
        let all_ancestors = List.map (Cpo.PODdg.get_ancestors ddg) all_treatment_variables
                            |> List.flatten in 
        let s' = List.fold_left (fun s k -> 
            if List.mem k all_ancestors 
            then s 
            else Ctxt.remove k s 
          ) s (Ctxt.bindings s |> List.map fst) in 
        let phi' = List.fold_left (fun p k -> 
            if List.mem k all_ancestors
            then p 
            else PHelp.remove_key p k
          ) in 
        (treatment_list, (s', phi'))
      ) tupes

    let rec get_constants program = 
      (* be conservative : something is constant only if it is the same in 
      every path. *)
      let constant_assignments = List.fold_left (fun lst path ->
        (* get non-random, non-external assignments *)
        let module Assignments = Map.Make(String) in 
        let multiple_assignments = ref Assignments.empty in 
        let constant_assignments = Utils.filter_map (fun n -> match n with 
            | Assign (o, k, {rand}, e) 
              when o <> Config.ExtSource && rand <> Config.Det -> 
              let s = Cpo.get_delta_key k in 
              if Cpo.is_constant e
              then if Assignments.mem s !multiple_assignments
                then begin
                  multiple_assignments := 
                    Assignments.add s true !multiple_assignments; 
                  Some s end
                else begin 
                  multiple_assignments := 
                    Assignments.add s false !multiple_assignments;
                    Some s end 
              else None 
            | _ -> None) path in 
        (* remove anything assigned twice *)
        List.filter (fun k -> Assignments.mem k !multiple_assignments) 
          constant_assignments)
        [] program in 
      (* filter out anything that isn't the same across *)
      Utils.filter_map (fun k ->
        let exprs = List.map (fun path -> 
          Utils.filter_map (fun n -> match n with 
            | Assign (_, k', _, e) -> if Cpo.get_delta_key k' = k 
              then Some e
              else None 
            | _ -> None) path) program in 
        if Utils.same exprs then Some k else None 
      ) constant_assignments

    let move_all_finals (tupes : (tmt list * cndst) list) = 
      List.map (fun (tmtlist, cndst) -> 
        (List.map (fun (d, r, p) -> 
            (* Printf.printf "treatments:\n%s\n" (
              Ctxt.bindings d
              |> Utils.join "\n" (fun (k, v) -> 
                  Printf.sprintf "\t%s=>%s" 
                  (Cpo.string_of_varidkey k)
                  (Cpo.string_of_cpo_expr v))
            ); *)
            let d', p' = move_finals d p in 
            (d', r, p'))
          tmtlist, cndst)
       ) tupes

    let smt_last_pass solver tupes = 
      let smt_per_cond_set (dt_list, (s, sphi)) = 
        SMT.push solver;
        let declared = ref Declared.empty in 
        (* Declare and assert conditioning set. *)
        SMTAux.push_cond_set solver declared s;
        (* Declare and assert unevaluated elements of the conditioning set. *)
        SMTAux.push_phi declared sphi;
        let dt_list' = List.map finalize_treatments dt_list in 
        let s', sphi' = finalize_conditioning_sets s sphi in 
        SMT.pop solver; 
        (dt_list', (s', sphi')) in 
      List.map smt_per_cond_set tupes

    let check_causal_sufficiency g plist tupes = 
      (* Printf.printf "number of paths: %d\nnumber of tupes: %d\n"
        (List.length plist) (List.length tupes); *)

      let module MySet = Set.Make(String) in 
      let ends = ref MySet.empty in 

      let rec unrecorded_synths_external_calls s cset : bool = 
        (* Precondition: we know that s is synthetic. *)
        (* Check referenced variables. *)
        let e = PathQueries.get_expr_for_assign s plist in 
        if Cpo.is_external_function e
        then true 
        else begin 
          let refs = Cpo.PODdg.get_parents g s in 
          let synths = refs 
            |> List.filter (fun ssaid -> 
                if OriginMap.mem ssaid !origin_map
                then OriginMap.find ssaid !origin_map = Config.Synth
                else false) in 
          (* Printf.printf "\n%s:%s [%s]; [%s]" 
            (Config.string_of_ssa_id s)
            (Format.string_of_inlang_expr e)
            (Utils.join ", " Config.string_of_ssa_id refs)
            (Utils.join ", " Config.string_of_ssa_id synths); *)
          let rec test_list lst : bool = match lst with 
            | [] -> false 
            | h::t -> 
              (* h is always a synthetic var *)
              if Ctxt.mem h cset 
              then 
                let e = PathQueries.get_expr_for_assign s plist in 
                (Cpo.condition_on e cset) && 
                  ((unrecorded_synths_external_calls h cset) || 
                    (test_list t))  
              else true 
            in   
          test_list synths
        end
        in 

      (* Because map and filter give me stack overflows here *)
      for i=0 to List.length plist - 1 do 
        let path = List.nth plist i in 
        for j=0 to List.length path - 1 do 
          let n = List.nth path j in 
          match n with 
          | Assign (_, (s, _), {corr=Config.End}, _) ->
            ends := MySet.add s !ends
          | _ -> ()
        done;
      done;

      let ends = MySet.elements !ends in 
      let csets = List.map snd tupes |> List.map fst in 
      for i=0 to List.length csets - 1 do 
        let cset : cpo_expr Ctxt.t = List.nth csets i in 
        let vars : Config.ssa_id list = Ctxt.keys cset in 
        for j=0 to List.length vars - 1 do 
          let k = List.nth vars j in 
          if OriginMap.find k !origin_map = Config.Synth 
            && List.mem (fst k) ends
            && unrecorded_synths_external_calls k cset 
          then raise (Static_errors.CausalSufficiencyError 
                        (Config.string_of_ssa_id k))
        done
      done


    (* TODO: Move this to inside the Phi module *)
    let get_phi_varnames (phi : Phi.t) : string list = 
      Phi.elements phi
      |> List.map Cpo.get_expr_vars
      |> List.flatten
      |> List.map fst
      
    let promote_phis tupes : (tmt list * cndst) list = tupes 
      |> List.map (fun (dtlist, (s, phis)) ->
          let dtlist : tmt list = dtlist
            |> List.map (fun (dt, r, dtphi) ->
              let concretized = Ctxt.bindings dt in 
              (* If anything is left in dtphi that also has a concrete version
                 in dt, this means that some dependency was not unique. *)
              let dt', dtphi' = List.fold_left (fun (dt, dtphi) (k, v) ->
                  if PHelp.has_key k dtphi 
                  then 
                    let pred = PHelp.get_expr k dtphi in 
                    let term = Cpo.expr_to_term v in 
                    if term = Smtlib.true_const 
                    then 
                      Ctxt.remove k dt, 
                      PHelp.remove_key dtphi k
                      |> PHelp.add (None, pred)
                    else if term = Smtlib.false_const
                    then 
                      Ctxt.remove k dt, 
                      PHelp.remove_name dtphi k
                      |> PHelp.add (None, Cpo.negate_expr pred)
                    else dt, dtphi
                else dt, dtphi
                ) (dt, dtphi) concretized in 
              dt', r, dtphi'
            ) in 
          let concretized = Ctxt.bindings s in 
          let phis' = List.fold_left (fun p (k, v) ->
              (* remove for now, promote later? *)
              if PHelp.has_key k p
              then PHelp.remove_key p k
              else p
            ) phis concretized in 
          (dtlist, (s, phis'))
        )

    let eval cfg g (p: program) : semantic_tuple list = 
      Logger.print_info __LINE__
        "Total paths through program: %d\n" (List.length p); 
      let (logged_paths, unlogged_paths) = 
        List.partition PathQueries.is_path_logged p in 


      let solver = SMT.make_solver Cpo.smt in 
      let constants = get_constants p in 
      SMT.push solver;
      declare_functions solver p;
      let logged_paths_evaled = logged_paths
        |> List.map (fun p -> (p, eval_path solver cfg p))  in
      SMT.pop solver;
      let no_randomization = List.filter (fun (p, _) -> 
        not (PathQueries.path_has_randomness p)) logged_paths_evaled in 
      (*let randomization = List.filter (fun (p, _) ->
        path_has_randomness p) unlogged_paths in *)
      
      if (List.length logged_paths = 0)
      then raise Static_errors.NotAnExperiment

      else if (List.length no_randomization > 0)
      then (raise (Static_errors.LoggedPathNoRandomization 
            (List.hd no_randomization |> fst)));

      check_causal_sufficiency g logged_paths
        (List.map snd logged_paths_evaled |> List.flatten);


      (Logger.print_info __LINE__
        "Logged paths through program: %d" (List.length logged_paths)); 
      let retval = 
        List.map snd logged_paths_evaled 
        |> List.flatten 
        |> move_all_finals
        (* |> smt_last_pass  *)
        (* |> filter_synthetic_vars *)
        |> promote_phis
        (* |> remove_non_dependents_from_conditioning_sets ddg *)
        |> convert_varidkeys
        |> merge_equivalent_conditioning_sets
        |> remove_constants constants in
      retval 
      
  (* Stuff that needs to be exported. *)
  let delta_key_from_node = DataStructOps.delta_key_from_node
  let is_path_logged = PathQueries.is_path_logged
end 
