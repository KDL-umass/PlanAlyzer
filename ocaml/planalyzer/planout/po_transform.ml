(** Dependendies: 
    - po_aux 
    - po_ddg
    - po_env
    - po_eval
    - po_format
    - po_normalize
    - po_syntax
    *)
(** Transforms a PlanOut program into a CorePO program. *)

module Logger = Logging.Make(struct 
    let file = __FILE__
    let phase = Logging.Corepo 
  end)

module Make (Settings : sig 
    val smt : string 
    val mock : bool
    val max_choices : int ref
    module POCfg : Config.Config 
      with type basetype = Po_syntax.base_type
    module PODdg : Ddg.Ddg 
      with type key = Po_env.env_key 
  end) : sig 
    module Corepo : Corepo.Corepo 
      with type inlang_expr = Po_syntax.po_expr
      and type typequals = Settings.POCfg.typequals
      and type graph = Settings.PODdg.outer
    module Static_errors : Exceptions.Staticbug
      with type node = Corepo.node 
      (*and type pi = Corepo.pi*)
      (*and type cpo_expr = Corepo.inlang_expr *)
    val transform : Settings.PODdg.outer -> Settings.POCfg.typequals ->  
      Po_syntax.program -> Corepo.program 
  end = struct  

    open Printf
    open Po_syntax  

    module Corepo : Corepo.Corepo 
      with type inlang_expr = Po_syntax.po_expr  
      and type typequals = Settings.POCfg.typequals 
      and type graph = Settings.PODdg.outer
      = Corepo.Make(struct
        open Smtlib
        type varidkey  = Po_env.env_key  
        type cpo_expr  = po_expr         
        type cpo_bexpr = po_bexpr        
        type cpo_uexpr = po_uexpr        
        type basetype  = base_type 

        type typequals = Settings.POCfg.typequals
        type graph = Settings.PODdg.outer

        exception RandomVariableChoiceFailure of po_sexpr * int 

        module Ctxt    = struct 
            include Po_env.Env.Delta
            let keys m = bindings m |> List.map fst 
          end 
        module POCfg   = Settings.POCfg
        module PODdg   = Settings.PODdg

        let env_convert env : Po_env.env = 
          List.fold_left (fun e (k, v) -> Po_env.add k v e) 
                   Po_env.empty
                   (Ctxt.bindings env)

        let is_constant = Po_aux.is_constant
        let is_random = function 
          | RandomVar _ 
          | CustomExpr (_, _, Some _) 
          | Aexpr (RandomNumber _)
          | Aexpr (CustomNumber (_, _, Some _))
          | Bexpr (RandomBoolean _)
          | Bexpr (CustomBoolean (_, _, Some _)) 
          | Cexpr (RandomContainer _)
          | Cexpr (CustomContainer (_, _, _, Some _))
          | Sexpr (RandomString _)
          | Sexpr (CustomString (_, _, Some _))
            -> true 
          | _ -> false 
        let rec condition_on e env = 
          let vars = Po_aux.get_node_vars (Expr e) in 
          let external_exists = 
            Utils.exists (fun v -> 
              not (Ctxt.mem v env) || 
                (condition_on (Ctxt.find v env) env)) 
              (Config.Params.elements vars) in  
          not (is_random e) && 
            (Po_aux.expr_external e <> None || external_exists)
        let rec is_final e = match e with 
          | Aexpr (PONumber _)
          | Bexpr (POBoolean _)
          | Sexpr (POString _) -> true 
          | Cexpr (POArray (_, arr)) -> 
            List.for_all is_final arr
          | Cexpr (POMap (_, m)) ->
            List.for_all is_final (POMap_.bindings m |> List.map snd)
          | _ -> false 
        let to_eq_rel (s, i) e = 
          Bexpr (match Po_aux.get_expression_type e with 
            | Unknown -> Equals (Get (Config.SrcUnknown, Delay, s, i), e)
            | Number -> BinNumOp (AEquals,
               GetNumber (Config.SrcUnknown, Delay, s, i),
               Po_syntax.to_number e)
            | Boolean -> BinBinOp (BEquals, 
               GetBoolean (Config.SrcUnknown, Delay, s, i),
               Po_syntax.to_boolean e)
            | Container -> BinCtrOp (CEquals, 
               GetContainer (Config.SrcUnknown, Delay, s, i, Unknown),
               Po_syntax.to_container e)
            | String -> BinStrOp (SEquals, 
               GetString (Config.SrcUnknown, Delay, s, i), 
               Po_syntax.to_string e))
        let replace_gets env e = 
          let rec helper_b e = match e with 
            | GetBoolean (_, _, s, i) ->
              let k = (s, i) in 
              if Ctxt.mem k env 
              then Ctxt.find k env |> Po_syntax.to_boolean 
              else e
            | Not e -> Not (helper_b e)
            | BinBinOp (op, e1, e2) -> BinBinOp (op, helper_b e1, helper_b e2)
            | _ -> e 
          and helper_a e = match e with 
            | GetNumber (_, _, s, i) ->
              let k = (s, i) in 
              if Ctxt.mem k env 
              then Ctxt.find k env |> Po_syntax.to_number 
              else e
            | _ -> e
          in
          match e with 
          | Bexpr e -> Bexpr (helper_b e)
          | Aexpr e -> Aexpr (helper_a e)
          | Get (_, _, s, i) -> 
            let k = (s, i) in 
            if Ctxt.mem k env then Ctxt.find k env else e 
          | _ -> Printf.printf "e: %s\n\t%s\n" (Po_format.string_of_expr e)
            (Po_format.ast_string_of_expr e); assert false 
        let eval_cpo_expr delta e =   
          Po_eval.eval_po_expr (env_convert delta) e 
        let get_expr_vars e = 
          Po_aux.get_node_vars (Expr e) |> Config.Params.elements
        let identifier_of_ssa_id (s, d) =
          Smtlib.Id (Printf.sprintf "%s_%d" s d)
        let get_expr_type ?(var=None) e = match var with
          | None -> Po_aux.get_expression_type e
          | Some v ->  
            begin match Po_aux.get_sub_expr  
                ~efn:(fun e -> match e with 
                       | Get (_, _, s, i) -> (s, i) = v
                       | _ -> false)
                ~afn:(fun e -> match e with 
                       | GetNumber (_, _, s, i) -> (s, i) = v
                       | _ -> false)
                ~bfn:(fun e -> match e with 
                       | GetBoolean (_, _, s, i) -> (s, i) = v
                       | _ -> false)
                ~cfn:(fun e -> match e with 
                       | GetContainer (_, _, s, i, _) -> (s, i) = v
                       | _ -> false)
                ~sfn:(fun e -> match e with 
                       | GetString (_, _, s, i) -> (s, i) = v
                       | _ -> false)
                e with 
              | None -> Unknown
              | Some e -> Po_aux.get_expression_type e 
            end 
        let randomly_split_worlds cfg e = match e with 
          | CustomExpr (_, _, Some _)
          | Aexpr (CustomNumber (_, _, Some _)) 
          | Bexpr (CustomBoolean (_, _, Some _)) 
          | Cexpr (CustomContainer (_, _, _, Some _)) 
          | Sexpr (CustomString (_, _, Some _)) -> 
            (* TODO: use codomain info from qualifiers here. *)
            [(e, Oratio.neg_one)]
          | RandomVar (POArray (_, weights), POArray (_, choices), _, salt)
          | Aexpr (RandomNumber (
            POArray (_, weights), POArray (_, choices), _,  salt))
          | Bexpr (RandomBoolean (
            POArray (_, weights), POArray (_, choices), _,  salt))
          | Cexpr (RandomContainer (
            POArray (_, weights), POArray (_, choices), _,  salt))
          | Sexpr (RandomString (
            POArray (_, weights), POArray (_, choices), _,  salt)) -> 
            let num_choices = List.length choices in 
            if num_choices < 2 
            then raise (RandomVariableChoiceFailure (salt, num_choices))
            else begin try
              List.combine choices 
                (List.map to_number weights 
                 |> List.map Po_syntax.number_to_ratio)
              with Po_syntax.NotFinal _ -> 
                List.map (fun e -> (e, Oratio.neg_one)) choices
            end
          | _ ->  
            (* This is an expression that's been marked random for being 
               downstream from a random variable. Just pass the expression 
               through. *)
            [(e, Oratio.one)]
         
        let show_index = true
        let string_of_cpo_expr = Po_format.string_of_expr ~show_index
        let string_of_cpo_bexpr b = 
          Po_format.string_of_expr ~show_index (Bexpr b)
        let string_of_varidkey (s, i) = Printf.sprintf "%s_%d" s i
        let varidkey_compare (s1, i1) (s2, i2) = 
          match compare s1 s2 with
          | 0 -> compare i1 i2
          | c -> c
        let smt = Settings.smt 
        let mock = Settings.mock
        let max_choices = Settings.max_choices 
        let rec id_of_base_type ?(aux_args=[]) = function
          | Boolean -> Some bool_sort
          | Number -> Some int_sort
          | String -> Some string_sort
          | Container ->
            ignore (if List.length aux_args > 0 then 
             Logger.print_debug __LINE__ 
               "aux_args: [%s]" 
               (Utils.join "; " string_of_base_type aux_args));
             begin match aux_args with
             | [_; Container] -> 
                raise (SMTError 
                  "Need to perform type inference on nested arrays.")
             | [dom; rng] ->
                 let t1 = id_of_base_type ~aux_args dom in 
                 let t2 = id_of_base_type ~aux_args rng in 
                 begin match t1, t2 with 
                   | Some t1, Some t2 -> Some (array_sort t1 t2)
                   | _ -> None 
                  end 
             | _ -> None
             end
          | Unknown -> None
        let rec custom_function_to_term name kvlist = 
          (*let args = List.map snd kvlist in 
          App (Id name, List.map expr_to_term args)*)
          const name 
        and expr_to_term = function 
          | Aexpr e -> aexpr_to_term e
          | Bexpr e -> bexpr_to_term e
          | Sexpr e -> sexpr_to_term e
          | CustomExpr _ ->
            (* To do: type inference on these, declare in Z3. For now, skip. *)
            bexpr_to_term (POBoolean true)
          | Get (_, _, s, i) -> const (string_of_varidkey (s, i))
          | e -> raise (SMTError ("expr not yet implemented: " ^         
                 (Po_format.string_of_expr e)))
        and make_get s i = Const (Id (string_of_varidkey (s, i)))
        and aexpr_to_term (aexpr : po_aexpr) : term = match aexpr with
          | NullNumber -> int_to_term 0
          | PONumber r -> int_to_term (Oratio.int_of_ratio r)
          | GetNumber (_, _, s, i) -> make_get s i 
          | Abinop (op, e1, e2) ->
             begin match op with
        	   | Sum -> add (aexpr_to_term e1) (aexpr_to_term e2)
        	   | Product -> mul (aexpr_to_term e1) (aexpr_to_term e2)
        	   | Mod -> raise (SMTError "mod not yet implemented")
        	   | Div -> raise (SMTError "div not yet implemented")
             end
          | CustomNumber _ -> raise (SMTError "unknown custom numeric term")
          | CoalesceNumber _ -> 
            raise (SMTError "aexpr to term coalesce numeric")
          | e -> assert false (*raise (SmtTermError (Aexpr e))*)
        and bexpr_to_term (bexpr : po_bexpr) : term = match bexpr with
          | NullBoolean -> bool_to_term false
          | POBoolean b -> bool_to_term b
          | GetBoolean (_, _, s, i) -> make_get s i
          | CustomBoolean (name, kvlist, _) -> 
            custom_function_to_term name kvlist
          | CoalesceBoolean (attempt, default) as e -> raise (SMTError  
            (sprintf "CoalesceBoolean not yet implemented: %s" 
            (Po_format.string_of_expr (Bexpr e))))
          | BIexpr _ -> raise (SMTError ("BIExpr not yet implemented: " ^
            (Po_format.string_of_expr (Bexpr bexpr))))
          | BinBinOp (op, e1, e2)
            ->
             begin match op with
        	   | And -> and_ (bexpr_to_term e1) (bexpr_to_term e2)
        	   | Or  -> or_ (bexpr_to_term e1) (bexpr_to_term e2)
        	   | e -> raise (SMTError "not yet implemented")
             end
          | BinNumOp (op, e1, e2) ->
             let e1' = aexpr_to_term e1 in
             let e2' = aexpr_to_term e2 in
             begin match op with
        	   | AEquals -> equals e1' e2' 
        	   | Gt -> gt e1' e2'
        	   | Lt -> lt e1' e2' 
             end
          | BinStrOp (op, e1, e2) ->
             let e1' = sexpr_to_term e1 in
             let e2' = sexpr_to_term e2 in
             begin match op with
        	   | SEquals -> equals e1' e2'
             end
          | Not e -> not_ (bexpr_to_term e)
          | Equals (e1, e2) -> equals (expr_to_term e1) (expr_to_term e2)
          | e -> raise (SMTError (Printf.sprintf "not yet implemented: %s" 
             (Po_format.string_of_expr (Bexpr e))))
        and sexpr_to_term (sexpr : po_sexpr) : term = match sexpr with
          | NullString -> string_to_term ""
          | POString s -> string_to_term s
          | GetString (_, _, s, i) -> make_get s i
          | CustomString (name, kvlist, _) -> 
            custom_function_to_term name kvlist
          | e -> raise (SMTError ("sexpr_to_term not yet implemented " ^ 
            (Po_format.string_of_expr (Sexpr e))))
        
        let term_to_bexpr (term : term) : po_bexpr =
          raise (SMTError (Printf.sprintf 
          "term that needs to be converted to bexpr: %s"
        			     (term_to_string term)))
        let bind_vars (bindings : (string * po_expr) list) (body : term) 
        : term =
          List.fold_left (fun t (k, v) -> Let (k, expr_to_term v, t))
        		 body
        		 bindings         
        let rec term_to_expr (term : term) = 
          let rec helper term = match term with
            | String s  -> Sexpr (POString s)
            | Const (Id "true") -> Bexpr (POBoolean true)
            | Const (Id "false") -> Bexpr (POBoolean false)
            | Const (Id s) -> 
              let (s, i) = Config.ssa_id_of_string s in 
              Get (Config.SrcUnknown, Delay, s, i)
            (*| Basetypes.Boolean, Int 0 -> Bexpr (POBoolean false)*)
            (*| Basetypes.Boolean, Int i when i > 0 -> Bexpr (POBoolean true)*)
            | Int i -> Aexpr (PONumber (Oratio.ratio_of_int i))
            | App (Id "and", lst) -> 
              Bexpr (List.fold_left (fun bexpr term ->
                BinBinOp (And, bexpr, helper term |> Po_syntax.to_boolean))
                (POBoolean true)
                lst)
            | App (Id "=", [left; right]) -> 
              Bexpr (Equals (helper left, helper right))
            | App (Id "not", [e]) ->
              Bexpr (Not (helper e |> to_boolean))
            | App (Id "or", lst) ->
              Bexpr (List.fold_left (fun bexpr term ->
                BinBinOp (Or, bexpr, helper term |> Po_syntax.to_boolean))
                (POBoolean false)
                lst)
            | _ -> raise (SMTError (Printf.sprintf 
              "Don't know how to handle term %s of type ??" 
              (string_of_term term))) in 
          let expr : cpo_expr = helper term in 
          let module Normalize = Po_normalize.MakeNormalize(Settings.POCfg) in 
          let (Program foo) = (Settings.POCfg.empty, Program (Expr expr))
                    |> Normalize.minimize_program
                    |> snd in 
          match foo with Expr e -> e |  _ -> assert false
        let and_expr e1 e2 = match e1, e2 with 
            | Bexpr b1, Bexpr b2 -> 
              Bexpr (BinBinOp (And, b1, b2))
            | Bexpr b, Get (o, m, s, i)
            | Get (o, m, s, i), Bexpr b -> 
              Bexpr (BinBinOp (And, b, GetBoolean (o, m, s, i)))
            | _, _ -> 
              Printf.printf "e1: %s; e2: %s\n" (string_of_cpo_expr e1) 
                (string_of_cpo_expr e2);
              assert false 
        let negate_expr e = match e with 
            | Bexpr b -> Bexpr (Not b)
            | CustomExpr _ ->
              Bexpr (POBoolean true)
            | e -> 
              Printf.printf "e: %s\n" (string_of_cpo_expr e);
              assert false
        let ast_string_of_id (s, i) = Printf.sprintf "(\"%s\", %d)" s i
        let ast_string_of_inlang_expr e = Po_format.ast_string_of_expr e
        let get_delta_key (s, i) = s
        let get_final_binding (s, i) ctxt : cpo_expr = 
          let init = (i, Ctxt.find (s, i) ctxt) in 
          Ctxt.bindings ctxt
          |> List.fold_left (fun (i, v) ((s', i'), v') ->
               if s' = s && i' > i then (i', v') else (i, v)
              ) init
          |> snd
        let external_function e = 
          match e, id_of_base_type (get_expr_type e) with 
          | CustomExpr             (name, kvlist, _),     Some t
          | Aexpr (CustomNumber    (name, kvlist, _)),    Some t
          | Bexpr (CustomBoolean   (name, kvlist, _)),    Some t
          | Cexpr (CustomContainer (name, kvlist, _, _)), Some t
          | Sexpr (CustomString    (name, kvlist, _)),    Some t ->
            Some (Smtlib.Id name, [], t)
          | _ -> None
        let is_pred e = match e with Bexpr _ -> true | _ -> false
        let cpo_expr_compare = compare 
        let is_opaque e = match e with 
          | Bexpr _ -> is_random e
          | _ -> true 
        let is_disjunction e = match e with 
          | Bexpr (BinBinOp (Or, _, _)) -> true
          | _ -> false
        let is_phi = Po_aux.is_phi
        let is_external_function = Po_aux.is_function

      end)

    module Static_errors = Corepo.Static_errors
    
    module Path_failures = struct 
      include Corepo
    
      let ensure_guard_varies = function
        | NullBoolean -> raise Static_errors.GuardAlwaysFalse
        | POBoolean b -> if b then raise Static_errors.GuardAlwaysTrue 
                          else raise Static_errors.GuardAlwaysFalse
        | _ -> ()
    
      let ensure_unique_choices salt = function 
        | POArray (_, arr) -> 
          if List.length arr <> (Utils.uniq arr |> List.length)
          then begin 
            let non_unique = List.filter (fun s -> 
              (List.filter ((=) s) arr |> List.length) > 1) arr in 
            raise (Static_errors.NonUniqueChoicesRV non_unique)
          end
        | _ -> ()
      
      let ensure_multiple_choices rvname = function 
        | POArray (_, arr) ->
          let numchoices = List.length arr in   
          if numchoices < 2 
          then raise (Static_errors.RandomVariableChoiceFailure (rvname, 
              numchoices))
        | _ -> ()
    
      let ensure_exists_path paths = 
        if List.length paths = 0 
        then raise Static_errors.NoPaths
    
      let ensure_static_return graph env return_arg =
        (*let anc = Program (Expr (Bexpr return_arg))
                  |> Ast.Po_aux.get_program_vars               
                  |> Ast.Po_aux.Params.elements *)
                  (* TODO: finish. *)
                  (* Additional logic to reason about when the return relies 
                  on external data from at least one path. *)
                  (*in *)
        let anc = [] in 
        if List.length anc <> 0 
        then raise (Static_errors.ReturnNotStaticallyDecidable anc)
      end 
    
    module PathSet = Set.Make(struct
      type t = Corepo.pi
      let compare (p1 : t) (p2 : t) =
        if (List.length p1) <> (List.length p2)
        then -1
        else List.combine p1 p2
             |> List.for_all (fun (n1, n2) -> n1 = n2)
             |> (fun tv -> if tv then 0 else -1)
      end)

    module LabelMap = Map.Make(String)
    let labelMap = ref LabelMap.empty 
    
    let make_conversion_error e = 
      Static_errors.ConversionError (e, Printf.sprintf
      "Expression %s is not a statement; 
      cannot be interpreted as a treatment, confounder/mediator, or assertion. 
      PlanAlyzer does not support expressions executed for side-effects."
      (Po_format.ast_string_of_expr e)
     ) 


    let is_assign n = match n with 
      | Corepo.Assign _ -> true
      | _ -> false 

    let is_assert n = match n with 
      | Corepo.Assert _ -> true 
      | _ -> false 

    let is_declare n = match n with 
      | Corepo.Declare _ -> true
      | _ -> false 

    let rec find_assign path k = match path with 
      | [] -> None 
      | h::t -> begin match h with 
        | Corepo.Assign (_, k', _, _) when k = k' -> Some h
        | _ -> find_assign t k 
      end 
    
    let rec find_declare path k = match path with 
      | [] -> None
      | (Corepo.Declare (k', _, _) as n)::t when k = k' -> Some n
      | _::t -> find_declare t k

    let get_assertion_expr n = match n with 
      | Corepo.Assert prop -> Some prop
      | _ -> None

    let rec get_ssids_from_prop prop = match prop with 
      | Corepo.Not prop -> get_ssids_from_prop prop
      | Corepo.And (prop1, prop2)
      | Corepo.Or (prop1, prop2) ->  
        get_ssids_from_prop prop1 @ (get_ssids_from_prop prop2)
      | Corepo.Id id -> [id]
      | _ -> []

    let get_cardinality node : Config.cardinality option = match node with 
      | Corepo.Assign (_, _, {Corepo.card}, _)
      | Corepo.Declare (_, {Corepo.card}, _) -> Some card
      | _ -> None 

    let get_randomness node : Config.randomness option = match node with 
      | Corepo.Assign (_, _, {Corepo.rand}, _)
      | Corepo.Declare (_, {Corepo.rand}, _) -> Some rand
      | _ -> None 

    let get_dynamism node : Config.dynamism option = match node with 
      | Corepo.Assign (_, _, {Corepo.dyn}, _) 
      | Corepo.Declare (_, {Corepo.dyn}, _) -> Some dyn 
      | _ -> None 

    let get_correlation node : Config.corr_t option = match node with 
      | Corepo.Assign (_, _, {Corepo.corr}, _) 
      | Corepo.Declare (_, {Corepo.corr}, _) -> Some corr
      | _ -> None 


    let propagate_card config prev_nodes curr_card cfg_card e = 
      let open Config in 
      match curr_card, cfg_card with 
      | _, High
      | High, _ -> High 
      | Low, Low -> begin match e with 
        | Aexpr _ -> 
          let open Corepo in 
          let vars = Po_aux.get_node_vars (Expr e) in
          let uses = Utils.filter_map (fun n -> match n with 
                      | Declare (k, {card}, _) 
                      | Assign (_, k, {card}, _) 
                        when Config.Params.mem k vars 
                          && card = High ->
                        Some card
                      | _ -> None
                     ) prev_nodes in 
          if List.length uses > 0 then High else Low 
        | Get (_, _, s, i) -> 
          (* Declarations haven't been added yet, so filtermap might be empty.*)
          let open Corepo in 
          Logger.print_debug __LINE__ 
            "Finding upstream reference for (%s, %d)" s i;
          Utils.filter_map (fun (n : node) -> match n with 
            | Declare (k, {card}, _)
            | Assign (_, k, {card}, _) when k = (s, i) ->
              Some card
            | _ -> None) prev_nodes
          (* Grab the last update. *)
          |> List.rev
          |> (function [] -> Low | h::_ -> h)
        | _ -> Low 
        end 

    let propagate_dynamism config prev_nodes t1 t2 e = 
      let inn = Po_aux.get_node_vars (Expr e) |> Config.Params.elements in 
      (* Find the dynamism labels for all of the incoming nodes. If at least
         one of them is time-varying, mark this node as time-varying. *)
      let dynamisms = Utils.filter_map (find_assign prev_nodes) inn
                      |> ((@) (Utils.filter_map (find_declare prev_nodes) inn))
                      |> Utils.filter_map get_dynamism in 
      let open Config in 
      match t1, t2 with 
      | Tv, _ 
      | _, Tv -> Tv
      | Const, Const -> 
        if Utils.exists ((=) Tv) dynamisms then Tv else Const 

    let propagate_corr config prev_nodes c1 c2 e = 
      let inn = Po_aux.get_node_vars (Expr e) |> Config.Params.elements in 
      let c2 = match c2 with 
        | Some c -> c 
        | None -> Config.End in 
      (* Find the dynamism labels for all of the incoming nodes. If at least
         one of them is time-varying, mark this node as time-varying. *)
      let correlations = Utils.filter_map (find_assign prev_nodes) inn
                      |> ((@) (Utils.filter_map (find_declare prev_nodes) inn))
                      |> Utils.filter_map get_correlation in 
      let open Config in 
      match c1, c2 with 
      | Exo, _ 
      | _, Exo -> Exo
      (* | _ -> End *)
      | End, End -> 
        if Utils.exists ((=) Exo) correlations then Exo else End

    let rec to_unit_list u = match u with 
      | Userid -> ["userid"]
      | Id s -> [s ^ "id"]
      | UnitR s -> [s]
      | UExpr e -> [Po_format.string_of_expr e]
      | Tuple2 (u1, u2) -> to_unit_list u1 @ (to_unit_list u2)
      | Tuple3 (u1, u2, u3) -> 
        to_unit_list u1 @ (to_unit_list u2) @ (to_unit_list u3)
      | Tuple4 (u1, u2, u3, u4) ->
        to_unit_list u1 @ (to_unit_list u2) @ (to_unit_list u3) @ 
          (to_unit_list u4)   

    (* let propagate_rand config prev_nodes r1 r2 e = 
      (* If any of the previous nodes are random, then this node is random.*)
      let open Config in 
      match r1, r2 with 
      | Rand u1, Rand u2 -> Rand (Utils.uniq (u1 @ u2))
      | Rand u, _ | _, Rand u -> Rand u
      | _, _ -> begin match e with 
        | RandomVar (_, _, unit_rand, _) 
        | Aexpr (RandomNumber (_, _, unit_rand, _))
        | Bexpr (RandomBoolean (_, _, unit_rand, _))
        | Cexpr (RandomContainer (_, _, unit_rand, _))
        | Sexpr (RandomString (_, _, unit_rand, _)) -> 
          Rand (to_unit_list unit_rand)
        | CustomExpr (name, kvlist, Some salt) ->
          let rec extract_units u = match u with 
            | Get (o, m, s, i) -> [s]
            | Cexpr (POArray (_, arr)) -> 
              List.map extract_units arr |> List.flatten 
            | _ -> 
              Printf.printf "Bad unit: %s\n" (Po_format.string_of_expr u);
            assert false in 
          let open Settings.POCfg in 
          let unit_arg = (Settings.POCfg.get_config name config).unit in 
          let unit_rand = List.assoc unit_arg kvlist |> extract_units in 
          Config.Rand unit_rand
        | _ -> begin 
            let open Corepo in 
            let uses = Po_aux.get_node_vars (Expr e) 
                       |> Config.Params.elements in 
            let rec helper nodes = match nodes with 
              | [] -> Det 
              | Declare (k, {rand}, _)::_ 
              | Assign (_, k, {rand}, _)::_ 
                when List.mem k uses -> rand
              | _::t -> helper t in
            match helper prev_nodes with 
              | Rand _ as r -> r
              | _ -> r1
          end
        end *)

    let config_to_qualifiers cfg s = 
      let open Settings.POCfg in 
      let {card; dynamism; randomness; domain; corr_t} = get_config s cfg in 
      let corr = match corr_t with Some c -> c | None -> Config.End in 
      Corepo.make_qualifiers ~card ~dyn:dynamism ~rand:randomness
                             ~corr:corr

    let get_randomness_from_expr parent_labels cfg e : Config.randomness = 
      let open Settings.POCfg in 
      let open Config in 
      let parent_rands = parent_labels
        |> List.map (fun c -> let open Corepo in c.rand) in
      let combine_rand_units = List.fold_left 
        (fun lst q -> match q with Rand u -> u @ lst | _ -> lst) in 
      match e with 
      | RandomVar              (_, _, unit, _) 
      | Aexpr (RandomNumber    (_, _, unit, _))
      | Bexpr (RandomBoolean   (_, _, unit, _))
      | Cexpr (RandomContainer (_, _, unit, _))
      | Sexpr (RandomString    (_, _, unit, _)) -> Rand (parent_rands
          |> combine_rand_units (to_unit_list unit)
          |> Utils.uniq)
      | CustomExpr             (name, kvlist,    Some {unit_value}) 
      | Aexpr (CustomNumber    (name, kvlist,    Some {unit_value}))
      | Bexpr (CustomBoolean   (name, kvlist,    Some {unit_value}))
      | Cexpr (CustomContainer (name, kvlist, _, Some {unit_value}))
      | Sexpr (CustomString    (name, kvlist,    Some {unit_value}))
        -> Rand (to_unit_list unit_value)
      | _ -> (match cfg.randomness with 
              | Rand _ -> Rand [cfg.unit]
              | _ -> if List.for_all (fun l -> l = Det) parent_rands
                     then Det
                     else Rand (combine_rand_units [] parent_rands 
                                |> Utils.uniq))

    let get_dynamism_from_expr parent_labels tqmap e : Config.dynamism = 
      let open Settings.POCfg in 
      let parent_dyns = parent_labels 
        |> List.map (fun c -> let open Corepo in c.dyn) in 
      match e with 
      | CustomExpr (name, _, _)
      | Aexpr (CustomNumber    (name, _,    _))
      | Bexpr (CustomBoolean   (name, _,    _))
      | Cexpr (CustomContainer (name, _, _, _))
      | Sexpr (CustomString    (name, _,    _)) -> 
        if (get_config name tqmap).dynamism = Config.Tv 
        then Config.Tv 
        else if Utils.exists (fun q -> q = Config.Tv) parent_dyns
        then Config.Tv
        else Config.Const
      | _ -> if Utils.exists (fun q -> q = Config.Tv) parent_dyns
        then Config.Tv
        else Config.Const 

    let get_correlation_from_expr 
        parent_labels
        (cfg : Settings.POCfg.config) 
        (rand: Config.randomness)  
        (e : Corepo.inlang_expr) : Config.corr_t = 
      let open Settings.POCfg in 
      let open Config in 
      (* If it's randomly assigned, then there is nothing in-script that could 
         make it correlated with outcome; this would have to come from the 
         specification (e.g., in the case of time-series experiments). *)
      let parent_corrs = parent_labels 
        |> List.map (fun q -> let open Corepo in q.corr) in 
      if rand <> Det 
      then begin match cfg.corr_t with 
          | None -> Exo 
          | Some corr -> corr 
          end 
      else begin match e with 
          | CustomExpr (name, _, _)
          | Aexpr (CustomNumber    (name, _,    _))
          | Bexpr (CustomBoolean   (name, _,    _))
          | Cexpr (CustomContainer (name, _, _, _))
          | Sexpr (CustomString    (name, _,    _)) -> begin 
              match cfg.corr_t with 
              | None -> End
              | Some c -> c 
              end 
          | _ -> begin match cfg.corr_t with 
            | None -> 
              if Utils.exists (fun c -> c = End) parent_corrs
              then End 
              else Exo
            | Some corr_t -> corr_t 
            end 
          end 
        
    let basetype_to_sort_option = function 
      | Unknown -> None
      | Number -> Some Smtlib.int_sort
      | Boolean -> Some Smtlib.bool_sort
      | Container -> None
      | String -> Some Smtlib.string_sort 

      
    let rec convert_bexpr_to_prop (e : po_bexpr) : Corepo.prop = match e with 
      | GetBoolean (_, _, s, i) -> Corepo.Id (s, i)
      | BinBinOp (And, e1, e2) -> 
        Corepo.And (convert_bexpr_to_prop e1, convert_bexpr_to_prop e2)
      | BinBinOp (Or, e1, e2) -> 
        Corepo.Or (convert_bexpr_to_prop e1, convert_bexpr_to_prop e2)
      | Not e -> Corepo.Not (convert_bexpr_to_prop e)
      | POBoolean true -> Corepo.True
      | POBoolean false -> Corepo.False
      | _ -> Printf.printf "%s\n" (Po_format.string_of_expr (Bexpr e)); 
       assert false

    let rec truncate_return (p : Corepo.pi) : Corepo.pi = match p with 
      | [] -> [Corepo.Return Corepo.True]
      | (Corepo.Return e)::t -> [Corepo.Return e]
      | h::t -> h::(truncate_return t)
 
    let rec make_paths_ast_node (p : Po_syntax.program) 
      (graph : Settings.PODdg.outer) (config : Settings.POCfg.typequals) 
      (n : Po_syntax.ast_node) : Corepo.program =
      match n with
      | Skip _ -> [[]]
      | Seq seqs -> (* Any of the seqs may contain a cond *)
         List.fold_left
           (* fold_left will pocess the nodes one at a time, in order.
              Each node will produce a list of paths *)
           (fun prefixes node ->
        	(* prefixes == all of the paths I've computed so far *)
  	      (* node == the current node I'm processing *)
  	      let suffixes = 
                (*List.map truncate_return *)
                  (make_paths_ast_node p graph config node) in
  	      (* Every prefix gets appended to very suffix.
  	      There should be (|prefixes| * |suffixes|) paths*)
  	      prefixes
  	      |> List.map (fun prefix -> 
                List.map (fun suffix -> prefix @ suffix) suffixes)
  	      |> List.concat
           ) 
           [[]] seqs
      | Cond conds ->
        let paths_in_cond ng n : Corepo.program =
          match ng with 
          | Guard g ->
            Path_failures.ensure_guard_varies g;
            let g = convert_bexpr_to_prop g in 
            List.map (fun path -> 
              (Corepo.Assert g)::path) 
              (make_paths_ast_node p graph config n)   
          | _ -> assert false
        in
        List.map (fun (g, n) -> paths_in_cond g n) conds
        |> List.fold_left (fun a b -> a @ b) [] 
      | Guard _ -> assert false
      | Assignment (o, s, i, e) -> 
      (* update this so it sets the default labels; then make labels later. *)
        let open Settings.POCfg in 
        let parents = Settings.PODdg.get_parents graph (s, i) in 
        let parent_labels = parents 
          |> Utils.filter_map (fun ssaid -> 
              let k = Config.string_of_ssa_id ssaid in 
              if LabelMap.mem k !labelMap 
              then Some (LabelMap.find k !labelMap)
              else ((*Printf.printf "\nKey %s not in label map\n" k;*) None)
            ) in 
        let cfg = get_config s config in 
        let rand = get_randomness_from_expr parent_labels cfg e in 
        (* let rand = if Po_aux.is_random_variable e then rand else Config.Det in  *)
        let dyn = get_dynamism_from_expr parent_labels config e in 
        (* let corr = get_correlation_from_expr parent_labels cfg rand e in *)
        let corr = if Po_aux.is_constant e || Po_aux.is_random_variable e 
          then Config.Exo else Config.End in
        let labels : Corepo.qualifiers = 
          Corepo.make_qualifiers ~card:cfg.card ~dyn ~rand ~corr in 
        labelMap := !labelMap
          |> LabelMap.add (Config.string_of_ssa_id (s, i)) labels;
        [[ Corepo.Assign (o, (s, i), labels, e) ]]
      | Return e -> [[ Corepo.Return (convert_bexpr_to_prop e) ]]
      | Expr e  -> raise (make_conversion_error e)


    let eval_path env (p : Corepo.pi) : Corepo.pi = 
      let open Corepo in 
      let rec minimize_prop env (e : prop) = match e with 
        | Not e' -> 
          begin match minimize_prop env e' with 
            | True -> False 
            | False -> True 
            | e'' -> Not e'' 
          end 
        | And (e1, e2) -> 
          begin match minimize_prop env e1, minimize_prop env e2 with 
            | False, _ | _, False -> False 
            | True, e | e, True -> e 
            | e1', e2' -> And (e1', e2')
          end 
        | Or (e1, e2) -> 
          begin match minimize_prop env e1, minimize_prop env e2 with 
            | True, _ | _, True -> True 
            | False, e | e, False -> e 
            | e1', e2' -> Or (e1', e2')
          end 
        | Id s -> 
          if Po_env.mem s env 
          then begin match Po_env.find s env with 
            | Bexpr (POBoolean true) -> True 
            | Bexpr (POBoolean false) -> False 
            | _ -> Id s 
            end 
          else Id s 
        | _ -> e in 
      let eval_node (env, path) (n : node) = match n with 
        | Assign (o, k, q, e) -> 
          (* Printf.printf "node: %s\nenv:%s\n" 
            (Corepo.Format.ast_string_of_path [n])
            (Po_env.string_of_env Po_format.string_of_expr env); *)
          let e' = Po_eval.eval_po_expr env e in 
          (Po_env.add ~o k e' env, Assign (o, k, q, e')::path)
        | Assert e -> (env, Assert (minimize_prop env e)::path)
        | _ -> (env, n::path) in       
      List.fold_left eval_node (env, []) p |> snd |> List.rev 

    let partial_eval (p : Corepo.program) : Corepo.program = 
      List.map (eval_path Po_env.empty) p

    let get_externals n = 
      let efn e = match e with 
        | Get (_, External, _, _) 
        | Get (Config.ExtSource, Random, _, _)
          -> true 
        | Phi (_, name, intlist) when List.mem 0 intlist -> true 
        | _ -> false in 
      let afn e = match e with 
        | GetNumber (_, External, _, _) 
        | GetNumber (Config.ExtSource, Random, _, _)
          -> true
        | _ -> false in 
      let bfn e = match e with 
        | GetBoolean (_, External, _, _) 
        | GetBoolean (Config.ExtSource, Random, _, _)
          -> true 
        | _ -> false in 
      let cfn e = match e with 
        | GetContainer (_, External, _, _, _) 
        | GetContainer (Config.ExtSource, Random, _, _, _)
          -> true 
        | _ -> false in 
      let sfn e = match e with 
        | GetString (_, External, _, _) 
        | GetString (Config.ExtSource, Random, _, _)
          -> true 
        | _ -> false in 
      let false_fn _ = false in 
      Po_aux.get_node_vars ~astfn:false_fn ~efn ~afn ~bfn ~cfn ~sfn n

    let get_declarations config (Program p) =
      get_externals p 
      |> Config.Params.elements
      |> List.filter (fun (s, i) -> i = 0) (* b/c of phi nodes. *)
      |> List.map (fun ((s, _) as ssaid) -> 
          let open Settings.POCfg in 
          let t = Po_aux.infer_var_type ~match_on_index:false ssaid (Program p) 
            |> basetype_to_sort_option in 
          let domain = match (get_config s config).domain with 
            | Var Unknown -> basetype_to_sort_option Unknown
            | Var t -> basetype_to_sort_option t
            | FnArg [] -> t
            | _ -> assert false in 
          let labels : Corepo.qualifiers = config_to_qualifiers config s in 
          labelMap := !labelMap
            |> LabelMap.add (Config.string_of_ssa_id ssaid) labels;
          Corepo.Declare (ssaid, labels, domain)
        )
    
    let make_labels g (prev_nodes : Corepo.pi) config n = 
          let open Settings.POCfg in 
          match n with 
            | Corepo.Assign (o, ((s, i) as k), 
              {Corepo.card; Corepo.rand; Corepo.dyn; Corepo.corr}, e) ->
              let cfg = get_config s config in 
              let parents = Settings.PODdg.get_parents g k in 
              Logger.print_debug __LINE__ 
                "Parents of %s: %s"
                (Config.string_of_ssa_id k)
                (Utils.join ", " Config.string_of_ssa_id parents)
                ;
              let get_random_units = function Config.Rand l -> l | _ -> [] in 
              (* Guards don't participate in the propagation of these labels... *)
    
              let parents_labels : Corepo.qualifiers list = Utils.filter_map
                 (fun k -> 
                    let id = Config.string_of_ssa_id k in 
                    if LabelMap.mem id !labelMap
                    then Some (LabelMap.find id !labelMap)
                    else None) parents in 
    
              let parents_units = parents_labels
                |> List.map (fun l -> let open Corepo in l.rand)
                |> List.fold_left (fun t r -> (get_random_units r) @ t) [] in 
              let parents_dynamism = 
                List.map (fun l -> let open Corepo in l.dyn) parents_labels in 
              let parents_correlation = 
                List.map (fun l -> let open Corepo in l.corr) parents_labels in 
              let rand = match rand with 
                | Config.Rand u -> Config.Rand (u @ parents_units |> Utils.uniq)
                | _ -> if not (Po_aux.is_constant e) || 
                          (List.length parents_units = 0) 
                       then Config.Det 
                       else Config.Rand (Utils.uniq parents_units) in 
              let dyn = match dyn with 
                | Config.Const -> 
                  if List.mem Config.Tv parents_dynamism 
                     || cfg.dynamism = Config.Tv
                  then Config.Tv else dyn
                | _ -> dyn in 

              (** TODO: is_constant is screwing things up -- need is_constant and has no parents. *)
              let corr = if List.length parents = 0 
                then Config.Exo
                else if rand = Config.Det then 
                match corr with 
                | Config.Exo ->
                  if List.mem Config.End parents_correlation 
                    || cfg.corr_t = Some Config.End
                  then Config.End else corr 
                | _ -> corr 
                else Config.Exo in 
              (* let card = propagate_card config prev_nodes card cfg.card e in 
              let rand = propagate_rand config prev_nodes rand cfg.randomness e in  *)
              let labels = Corepo.make_qualifiers ~card ~dyn ~rand ~corr in 
              labelMap := !labelMap 
                |> LabelMap.add (Config.string_of_ssa_id (s, i)) labels;
              Corepo.Assign (o, k, labels, e) 
            | _ -> n
      
    let update_labels (g : Settings.PODdg.outer) config path = 
      let rec helper acc path = match path with 
          | [] -> acc
          | h::t -> helper (acc @ [make_labels g acc config h]) t in 
        helper [] path 

    (* let update_labels (g : Settings.PODdg.outer) config path = 
      (* Nodes downstream from assertions that are end or rand need to be 
         updated *)
      let assertion_labels : Config.ssa_id list list = path 
        |> Utils.filter_map get_assertion_expr
        (* Get the variables in each of the assertion node expressions *)
        |> List.map get_ssids_from_prop in 
      
      (* Helper function that takes in a collection of nodes from an expression
         and *)
      path *)

    let return_symbolic_to_concrete (p : Corepo.program) =
      let open Corepo in 
      List.map (fun pi -> match List.rev pi with 
       | (Return True)::_ | (Return False)::_ -> pi 
       | (Return b)::t -> List.rev t @ [Assert b; Return True]
       | _ -> assert false)
       p

    let filter_data_impossible_flow (p : Corepo.program) = 
      let open Corepo in 
      List.filter (fun pi -> 
        (* If we can run constant propagation on any of the asserts *) 
        List.filter (fun n -> n = Assert False) pi
        |> List.length 
        |> ((=) 0)
      ) p

    (* let update_phi_labels (p : Corepo.program) : Corepo.program = 
      (* Get all the names that have phi nodes. *)
      let phis : (string * int * int list) list = p
        |> List.flatten
        |> Utils.filter_map (fun n -> match n with 
            | Corepo.Assign (_, (_, i), _,  Phi (_, name, ints)) -> 
              Some (name, i, ints)
            | _ -> None) 
        |> Utils.uniq in 
      (* For each phi node, get the previous definitions' randomness labels 
         across all paths. *)
      let find_labels (s, _, int_list) = 
        Utils.filter_map (fun node ->  
          match node with 
            | Corepo.Assign (_, (s', j), l, _) -> 
              if s = s' && List.mem j int_list 
              then Some (j, l)
              else None 
            | _ -> None) 
          (List.flatten p) in 
      let labels = List.map (fun ((s, i, _) as t) -> 
        ((s, i), find_labels t)) phis in 
      (* Printf.printf "labels: [%s]\n" (Utils.join "\n" (fun ((s, i), lst) ->
        Printf.sprintf "%s_%d [%s]" s i (Utils.join "; " (fun (i, r) -> 
          Printf.sprintf "(%d, %s)" i (Config.sexp_of_randomness r |> Sexplib.Sexp.to_string)) lst))
          labels); *)
      let rec set_one s refs = 
        let dep_phis, refs = List.partition (fun (j, _) ->
          List.mem_assoc (s, j) labels) refs in 
        let dep_phis = dep_phis 
          |> List.map (fun (j, _) -> 
              List.assoc (s, j) labels |> set_one s) in 
        let rands, dets = List.partition (fun (j, {Corepo.rand}) -> 
            match rand with Config.Rand _ -> true | _ -> false) 
          refs in 
        match List.length rands, List.length dets, List.length phis with
          | 0, _, 0 -> Config.Det
          | _, 0, 0 -> Config.Rand 
                (List.map 
                  (fun (_, {Corepo.rand=Config.Rand u}) -> u) rands 
                 |> List.flatten 
                 |> Utils.uniq)
          | _, _, n -> 
            assert (n > 0);
            let rand_list = rands
              |> List.map 
                  (fun (j, {Corepo.rand=Config.Rand u}) -> (j, u)) 
              |> List.fold_left (fun lst (i, ulist) -> 
                  if List.mem_assoc i lst 
                  then (i, List.assoc i lst 
                           |> (@) ulist
                           |> Utils.uniq)::lst
                  else (i, ulist)::lst 
                 ) []
              |> (@) (Utils.filter_map (fun r -> match r with 
                         | Config.CS {rands} -> Some rands
                         | _ -> None) dep_phis
                      |> List.flatten)
              |> Utils.uniq in 
            let det_list = List.map fst dets 
              |> (@) (Utils.filter_map (fun r -> match r with 
                         | Config.CS {dets} -> Some dets
                         | _ -> None) dep_phis
                      |> List.flatten) 
              |> Utils.uniq in 
            if List.length rand_list = 0
            then Config.Det
            else if List.length det_list = 0 
            then 
              Config.Rand (List.map snd rand_list |> List.flatten |> Utils.uniq)
            else Config.CS {dets = det_list; rands = rand_list} in 
      List.map (fun path -> 
        List.map (fun n -> match n with 
          | Corepo.Assign (o, (s, i), 
              {Corepo.corr; Corepo.dyn; Corepo.card}, 
              (Phi _ as e)) as n' -> 
            if List.mem_assoc (s, i) labels 
            then 
              let refs = List.assoc (s, i) labels in             
              let rand_label = set_one s refs in 
              let dyn_label : Config.dynamism = 
                  if List.exists (fun (_, {Corepo.dyn}) -> dyn = Config.Tv) refs 
                  then Config.Tv else Config.Const in 
              let corr_label =
                  if List.exists (fun (_, {Corepo.corr}) -> corr = Config.End) refs
                  then Config.End else Config.Exo in 
              Corepo.Assign (o, (s, i), {Corepo.card; 
                                         Corepo.dyn=dyn_label; 
                                         Corepo.corr=corr_label; 
                                         Corepo.rand=rand_label}, 
                                         e)
            else n'
          | _ -> n
          ) path
        ) p  *)

    let transform (g : Settings.PODdg.outer) (config: Settings.POCfg.typequals) 
      (p : Po_syntax.program) : Corepo.program = 
      (* This will remove the Seq nodes and replace them with a list *)
      let declarations = get_declarations config p in 
      let (Program p') = p in 
      let (paths : Corepo.program) = 
        List.fold_left 
          (fun s path -> PathSet.add path s) 
          PathSet.empty 
          (make_paths_ast_node p g config p')
        |> PathSet.elements
        |> List.map truncate_return 
        (* |> update_phi_labels          *)
        |> partial_eval 
        |> return_symbolic_to_concrete 
        |> partial_eval
        |> filter_data_impossible_flow 
        in
      if List.length paths > 0 && 
        (List.for_all (fun p -> List.length p > 0) paths)
      then Utils.uniq paths 
           |> List.map (fun p -> declarations @ p)
           |> List.map (update_labels g config)
      else raise Static_errors.NoPaths
  
  end
