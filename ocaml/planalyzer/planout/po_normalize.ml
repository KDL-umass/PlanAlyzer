(** Dependencies:
    - po_aux
    - po_counters
    - po_env
    - po_eval
    - po_format
    - po_parse
    - po_syntax
*)
module Logger = Logging.Make(struct 
    let file = __FILE__
    let phase = Logging.Normalize
  end)

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
                      ?efn:(Po_syntax.po_expr  -> Po_syntax.po_expr) ->
                      ?afn:(Po_syntax.po_aexpr -> Po_syntax.po_aexpr) ->
                      ?bfn:(Po_syntax.po_bexpr -> Po_syntax.po_bexpr) ->
                      ?cfn:(Po_syntax.po_cexpr -> Po_syntax.po_cexpr) ->
                      ?sfn:(Po_syntax.po_sexpr -> Po_syntax.po_sexpr) ->
                      program -> program
  val normalize : typequals -> program -> (typequals * program)
  val constant_propagation : (typequals * program) -> (typequals * program)
  val minimize_program : (typequals * program) -> (typequals * program)
  val constant_min_steady : (typequals * program) -> (typequals * program)
  val specialize_steady : varid:(unit -> string) -> (typequals * program) -> 
    (typequals * program)
  val linearize_fn_app : varid:(unit -> string) -> 
    (typequals * program) -> (typequals * program)
  val linearize_steady : varid:(unit -> string) -> (typequals * program) -> 
    (typequals * program)
  val lift_random_variables : varid:(unit -> string) -> 
    (typequals * program) -> (typequals * program)
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
  = struct
    include Po_syntax
    type env = Po_aux.env
    open Config 
    module POConfig = POCfg
    type typequals = POCfg.typequals
    module Parse = Po_parse.MakeParse(POCfg)

    exception Debug
    exception Empty_domain of po_expr 
    exception Static_unit_error of string * po_expr 
    exception Unit_constant of po_expr 

    let reset_varid _ = Po_counters.renew_uid "varid"
    let reset_skipid _ = Po_counters.renew_uid "skipid"

    let extract_by_key = Po_eval.extract_by_key
    let flatten_seqs = Po_aux.flatten_seqs

    (*let varid = Counters.thread_safe_copy ~prefix:"fv" "varid"*)
    let skipid = Po_counters.skipid

    let pomap_from_list (l : (string * po_expr) list) = 
      List.fold_left (fun m (k, v) -> POMap_.add k v m) POMap_.empty l

    let tree_rewrite ?(breadth=true)
                    ?(astfn=fun (n : ast_node) -> n)
                    ?(efn=fun (e: po_expr) -> e)
                    ?(afn=fun (e: po_aexpr) -> e)
                    ?(bfn=fun (e: po_bexpr) -> e)
                    ?(cfn=fun (e: po_cexpr) -> e)
                    ?(sfn=fun (e: po_sexpr) -> e)
                    (program : program) : program = 
      let (Program p) = program in 
      let hcustom (type t) (ctor : string -> kvlist -> t) fn s e : t =
        ctor s (List.map (fun (s, e) -> (s, fn e)) e) in 
      let convert rewriter f = 
        if breadth then
          (fun argument -> rewriter (f argument))
        else
          (fun argument -> f (rewriter argument)) in
      let rec rewrite_node_impl node = match node with 
        | Skip _ as n' -> n'
        | Seq seqs -> Seq (List.map rewrite_node seqs)
        | Guard g -> Guard (rewrite_bexp g)
        | Cond conds -> 
          Cond (List.map (fun (a, b) -> (rewrite_node a, rewrite_node b)) conds)
        | Assignment (o, s, i, e) -> Assignment (o, s, i, rewrite_exp e)
        | Return b -> Return (rewrite_bexp b)
        | Expr e -> Expr (rewrite_exp e)          
      and rewrite_node node = convert rewrite_node_impl astfn node
      and rewrite_exp_impl exp = 
        match exp with
          | Null | Phi _ | Get _ as e' -> e'
          | Aexpr a -> Aexpr (rewrite_aexp a)
          | Bexpr b -> Bexpr (rewrite_bexp b)
          | Cexpr c -> Cexpr (rewrite_cexp c)
          | Sexpr s -> Sexpr (rewrite_sexp s)
          | CustomExpr (s, kvlist, salt) ->
            hcustom (fun s l -> CustomExpr (s, l, salt)) rewrite_exp s kvlist
          | Coalesce (a, d) -> Coalesce (rewrite_exp a, rewrite_exp d)
          | Iexpr (b, i) -> Iexpr (rewrite_cexp b, rewrite_exp i)
          | RandomVar (w, c, u, s) -> 
            RandomVar (rewrite_cexp w, rewrite_cexp c, u, s)
      and rewrite_exp exp = convert rewrite_exp_impl efn exp
      and rewrite_aexp_impl aexp = 
        match aexp with
          | NullNumber | PONumber _ | GetNumber _ as a' -> a'
          | CustomNumber (s, kvlist, salt) ->
            hcustom (fun s l -> CustomNumber (s, l, salt)) rewrite_exp s kvlist
          | RandomNumber (weights, choices, u, s) ->
            RandomNumber (rewrite_cexp weights, rewrite_cexp choices, u, s)
          | CoalesceNumber (a, d) ->
            CoalesceNumber (rewrite_aexp a, rewrite_aexp d)
          | AIexpr (b, i) -> AIexpr (rewrite_cexp b, rewrite_exp i)
          | Length c -> Length (rewrite_cexp c)
          | Abinop (op, left, right) -> 
            Abinop (op, rewrite_aexp left, rewrite_aexp right)        
      and rewrite_aexp aexp = convert rewrite_aexp_impl afn aexp
      and rewrite_bexp_impl bexp =
        match bexp with
          | NullBoolean | POBoolean _ | GetBoolean _ as b' -> b'
          | CustomBoolean (s, kvlist, salt) -> 
            hcustom (fun s l -> CustomBoolean (s, l, salt)) rewrite_exp s kvlist
          | RandomBoolean (weights, choices, u, s) ->
            RandomBoolean (rewrite_cexp weights, rewrite_cexp choices, u, s)
          | CoalesceBoolean (attempt, default) ->
            CoalesceBoolean (rewrite_bexp attempt, rewrite_bexp default)
          | BIexpr (base, index) ->
            BIexpr (rewrite_cexp base, rewrite_exp index)
          | Not e -> Not (rewrite_bexp e)
          | Equals (left, right) -> Equals (rewrite_exp left, rewrite_exp right)
          | BinBinOp (op, left, right) -> 
            BinBinOp (op, rewrite_bexp left, rewrite_bexp right)
          | BinStrOp (op, left, right) -> 
            BinStrOp (op, rewrite_sexp left, rewrite_sexp right)
          | BinCtrOp (op, left, right) -> 
            BinCtrOp (op, rewrite_cexp left, rewrite_cexp right)
          | BinNumOp (op, left, right) -> 
            BinNumOp (op, rewrite_aexp left, rewrite_aexp right)
      and rewrite_bexp bexp = convert rewrite_bexp_impl bfn bexp
      and rewrite_cexp_impl cexp = 
        match cexp with
          | NullContainer | GetContainer _ as c' -> c'
          | POArray (t, arr) -> POArray (t, List.map rewrite_exp arr)
          | POMap (t, m) -> POMap (t, POMap_.map rewrite_exp m)
          | CustomContainer (s, kvlist, t, salt) ->
            hcustom (fun s l -> 
              CustomContainer (s, l, t, salt)) rewrite_exp s kvlist
          | RandomContainer (weights, choices, u, s) ->
            RandomContainer (rewrite_cexp weights, rewrite_cexp choices, u, s)
          | CoalesceContainer (a, d) -> 
            CoalesceContainer (rewrite_cexp a, rewrite_cexp d)
          | CIexpr (b, i) -> CIexpr (rewrite_cexp b,rewrite_exp i)
          | Range (min, max) -> Range (rewrite_aexp min, rewrite_aexp max)
          | Repeat (times, item) -> 
            Repeat (rewrite_aexp times, rewrite_exp item)
          | EnumChoose (sample, size) -> 
            EnumChoose (rewrite_cexp sample, rewrite_aexp size)
      and rewrite_cexp cexp = convert rewrite_cexp_impl cfn cexp
      and rewrite_sexp_impl sexp = 
        match sexp with
          | NullString | POString _ | GetString _ as s' -> s'
          | CustomString (s, kvlist, salt) -> 
            hcustom (fun s l -> CustomString (s, l, salt)) rewrite_exp s kvlist
          | RandomString (weights, choices, u, s) ->
            RandomString (rewrite_cexp weights, rewrite_cexp choices, u, s)
          | CoalesceString (a, d) -> 
            CoalesceString (rewrite_sexp a, rewrite_sexp d)
          | SIexpr (b, i) -> SIexpr (rewrite_cexp b, rewrite_exp i)
      and rewrite_sexp sexp = convert rewrite_sexp_impl sfn sexp
      in 
      Program (rewrite_node p)

    let constant_propagation (config, program) =
      let env = ref Po_env.empty in 
      let astfn n = match n with 
        | Assignment (o, s, i, e) ->
          env := Po_env.add ~o (s, i) e !env; n
        | _ -> n in 
      let get_match_fn (type t) m s i (e : t) convert = 
        if m = Unclassified 
        then begin
            (* print_debug __LINE__ (Printf.sprintf "%s\n" 
              (Po_env.string_of_env Po_format.string_of_expr !env)); *)
            if Po_env.mem (s, i) !env 
            then 
              let e' = Po_env.find (s, i) !env in 
              if Po_aux.is_constant e'
              then convert e'
              else e
            else e 
          end 
        else e in 
      let efn e = match e with 
        | Get (_, m, s, i) -> get_match_fn m s i e (fun e -> e)
        | _ -> e in 
      let afn e = match e with 
        | GetNumber (_, m, s, i) -> get_match_fn m s i e to_number
        | _ -> e in 
      let bfn e = match e with 
        | GetBoolean (_, m, s, i) -> get_match_fn m s i e to_boolean
        | _ -> e in 
      let cfn e = match e with 
        | GetContainer (_, m, s, i, _) -> get_match_fn m s i e to_container
        | _ -> e in 
      let sfn e = match e with 
        | GetString (_, m, s, i) -> get_match_fn m s i e to_string 
        | _ -> e in 
      (config, tree_rewrite ~astfn ~efn ~afn ~bfn ~cfn ~sfn program)

    let minimize_program (config, program) =
      (* Minimize anything that can be reduced statically. *)
      let rec array_from_range (min : po_aexpr) (max : po_aexpr) : po_cexpr =
        match min, max with
        | PONumber nmin, PONumber nmax ->
          let nmin' = Oratio.int_of_ratio nmin in
          let nmax' = Oratio.int_of_ratio nmax in
          let diff = nmax' - nmin' in
          Utils.range (diff + 1)
          |> List.map ((+) nmin')
          |> List.map (fun n -> Aexpr (PONumber (Oratio.ratio_of_int n)))
          |> (fun arr -> POArray (Po_syntax.Number, List.rev arr))
        | min', max' -> Range (min', max') 
      and array_from_repeat (num_times : po_aexpr) (item : po_expr) : po_cexpr =
        match num_times, item with
        | PONumber n, item' ->
          let n' = Oratio.int_of_ratio n in
          Utils.range n'
          |> List.map (fun _ -> item')
          |> (fun arr -> POArray (Po_aux.get_expression_type item', arr))
        | Length c, item' ->
          begin
            match  c with
            | POArray (t, arr) -> 
              let n = List.length arr |> Oratio.ratio_of_int in 
              array_from_repeat (PONumber n) item'
            | POMap (t, m) -> 
              let n = POMap_.cardinal m |> Oratio.ratio_of_int in 
              array_from_repeat (PONumber n) item'
            | c' -> Repeat (Length c', item')
          end
        | num_times', item' -> Repeat (num_times', item) in 
      let cfn e = match e with 
        | CIexpr (base, index) -> 
          extract_by_key (fun b i -> CIexpr (b, i)) 
            Po_syntax.to_container base index
        | Range (min, max) -> array_from_range min max
        | Repeat (num_times, item) -> array_from_repeat num_times item
        | e -> e in 
      let efn e = match e with 
        | Iexpr (base, index) ->
          extract_by_key (fun b i -> Iexpr (b, i)) (fun e -> e) base index
        | _ -> e in 
      let sfn e = match e with 
        | SIexpr (base, index) -> 
          let ctor base index = SIexpr (base, index) in 
          extract_by_key ctor Po_syntax.to_string base index 
        | e -> e 
      and bfn e = match e with 
        | BinStrOp (SEquals, POString s1, POString s2) -> POBoolean (s1 = s2)
        | BinCtrOp (CEquals, POMap (_, m1), POMap (_, m2)) -> 
          POBoolean (m1 = m2)
        | BinCtrOp (CEquals, POArray (_, a1), POArray (_, a2)) -> 
          POBoolean (a1 = a2)
        | BinNumOp (op, PONumber r1, PONumber r2) -> 
          POBoolean (match op with 
            | AEquals -> Oratio.equals r1 r2  
            | Lt -> Oratio.lt r1 r2  
            | Gt -> Oratio.gt r1 r2)
        | BinBinOp (op, POBoolean b1, POBoolean b2) ->
          POBoolean (match op with 
            | And -> b1 && b2
            | Or -> b1 || b2
            | BEquals -> b1 = b2)
        | Not (Not e) -> e
        (* Only one side minimized. *)
        | BinBinOp (op, POBoolean b, e)
        | BinBinOp (op, e, POBoolean b) -> 
          begin match op with 
            | And -> if b then e else POBoolean false
            | Or -> if b then POBoolean true else e
            | BEquals -> if b then e else Not e
          end
        | Not POBoolean true -> POBoolean false
        | Not POBoolean false -> POBoolean true
        | _ -> e in 
      let afn e = match e with 
        | Length POArray (t, arr) -> 
          PONumber (List.length arr |> Oratio.ratio_of_int)
        | Length POMap (t, m) ->
          PONumber (POMap_.cardinal m |> Oratio.ratio_of_int)
        | AIexpr (base, index) ->
          let ctor base index = AIexpr (base, index) in 
          extract_by_key ctor Po_syntax.to_number base index
        | Abinop _ -> Po_eval.sort e
        | _ -> e 
      in (config, tree_rewrite ~efn ~afn ~bfn ~cfn ~sfn program)

    let constant_min_steady tupe = 
      let update = ref true in 
      let program = ref (snd tupe) in 
      let cfg = fst tupe in 
      while !update do
        let (_, program') = constant_propagation (cfg, !program) 
                            |> minimize_program in 
        if program' = !program 
        then update := false
        else program := program'
      done;
      (fst tupe, !program)        
        
    let linearize_fn_app ~varid (config, program) = 
    (* Compares the fresh variable names -- since it is a lexicographic 
        comparison, fv10 < fv9. All fresh variables have the same prefix, so 
        first compare string length, which is equivalent to comparing the width 
        of a number. If two numbers have the same width, then we compare them 
        lexicographically. *)
      let cmp k1 k2 =           
        let l1 = String.length k1 in 
        let l2 = String.length k2 in 
        if l1 < l2 
        then -1 
        else if l1 > l2
        then 1 
        else compare k1 k2 in 
      (* This functor stores the expressions that the fresh variables point to. 
        The first pass in linearization will replace expressions with their 
        reference labels, and add the reference label (i.e., fresh variable) and 
        its corresponding expression to this Map. In the second pass, non-
        external free variables will have their definitions injected at the top 
        of the code block. *) 
      let module Fvmap = Map.Make(struct 
          type t = string 
          let compare = cmp 
        end) in 
      let fvmap = ref Fvmap.empty in 
      (* If the input expression e is a function or a relation, this function 
        creates a fresh variable representing e, stores that fresh variable and 
        e in the fresh variable map, and returns a new label reference. 
        Otherwise, the function simply returns the input expression e. *)
      let fn (type t) (e : t) (convert : t -> po_expr) 
            (ctor : origin -> getref -> string -> int -> t) : t = 
        let e' = convert e in 
        if Po_aux.is_function e' || Po_aux.is_relation e'
        then begin 
            let r = varid () in 
            let i = 1 in 
            Logger.print_debug __LINE__ "linearizing %s %d %s\n" 
              r i (Po_format.string_of_expr e');
            fvmap := Fvmap.add r e' !fvmap;
            ctor Synth Unclassified r i
          end 
        else e in 
      let astfn n = match n with 
        | Return bexpr ->
          Return (fn bexpr (fun e -> Bexpr e) 
            (fun o m s i -> GetBoolean (o, m, s, i)))
        | Guard bexpr -> 
          Guard (fn bexpr (fun e -> Bexpr e) 
            (fun o m s i -> GetBoolean (o, m, s, i)))
        | _ -> n in 
      let fresh_vars_printed = ref [] in 
      let ast_inject n = match n with 
        | Return _
        | Cond _ 
        | Assignment _ -> begin
          let vars = Po_aux.get_program_vars (Program n) in
          let var_list = Config.Params.elements vars in 
          if not (Config.Params.equal vars 
            (Config.Params.of_list !fresh_vars_printed))
          then begin 
            Logger.print_debug __LINE__ 
              "All fresh variables generated so far: [%s]
              \n\t\tVariables in this expression: [%s]" 
                (Utils.join "; " Utils.identity 
                  (Fvmap.bindings !fvmap |> List.map fst))
                (Utils.join "; " fst var_list);
            fresh_vars_printed := var_list
          end; 
          (* All of the generated variables directly referenced. *)
          let fv_direct = Po_aux.get_program_vars (Program n)
                          |> Config.Params.elements 
                          |> List.map fst 
                          |> List.filter (fun s -> Fvmap.mem s !fvmap) in
          (* Function to recursively fetch fresh variables referenced. *)
          let rec fv_ref fv : string list  = 
              let fvs = Po_aux.get_node_vars (Expr (Fvmap.find fv !fvmap)) 
                        |> Config.Params.elements
                        |> List.map fst
                        |> List.filter (fun s -> Fvmap.mem s !fvmap) in  
              if fvs = [] 
              then fvs
              else fvs @ (List.map fv_ref fvs |> List.flatten) in 
          let fvs = List.map fv_ref fv_direct
                    |> List.flatten
                    |> (@) fv_direct
                    |> Utils.uniq 
                    |> List.sort cmp in 
          if List.length fvs > 0 
          then Logger.print_debug __LINE__ "%s" 
            (Utils.join ", " Utils.identity fvs);
          let fvvals = List.map (fun s -> Fvmap.find s !fvmap) fvs in 
          ignore (List.map (fun s -> fvmap := Fvmap.remove s !fvmap) fvs);
          Seq (List.map (fun (s, e) -> Assignment (Synth, s, 1, e)) 
                        (List.combine fvs fvvals) @ [n] 
              |> flatten_seqs) 
          end 
        | _ -> n in
      (* Assignments end up in guards and need to be lifted out. *)
      let split_guard g : (ast_node list * ast_node) = match g with 
        | Seq seqs1 -> begin match List.rev seqs1 with 
            | Guard g::assigns -> (assigns, Guard g)
            | _ -> ([], g) 
          end
        | Guard _ -> ([], g)
        | _ -> assert false in 
      let rec lift_rel_guard n : ast_node = match n with 
        | Cond conds -> 
          let (guard, conds) = List.split conds in 
          let conds = List.map lift_rel_guard conds in 
          let (assigns, gs) = List.map split_guard guard |> List.split in 
          Seq (List.concat assigns @ [Cond (List.combine gs conds)])
        | Seq seqs -> Seq (List.map lift_rel_guard seqs |> flatten_seqs)
        | _ -> n in 
      let open Po_syntax in 
      let efn e = match e with 
        | CustomExpr (s, kvlist, salt) ->
          CustomExpr (s, List.map (fun (k, v) -> 
            (k, fn v Utils.identity eget_ctor)) kvlist, salt)
        | Coalesce (attempt, default) -> 
          Coalesce (fn attempt Utils.identity eget_ctor,
                    fn default Utils.identity eget_ctor)
        | Iexpr (base, index) -> 
          Iexpr (fn base from_container (cget_ctor Unknown), 
                fn index Utils.identity eget_ctor)
        | RandomVar (weights, choices, unit, salt) ->
          RandomVar (fn weights from_container (cget_ctor Unknown),
                    fn choices from_container (cget_ctor Unknown),
                    unit, salt)
        | _ -> e in 
      let afn e = match e with 
        | CustomNumber (s, kvlist, salt) -> 
          CustomNumber (s, List.map (fun (k, v) ->
            (k, fn v Utils.identity eget_ctor)) kvlist, salt)
        | CoalesceNumber (attempt, default) ->
          CoalesceNumber (fn attempt from_number aget_ctor,
                          fn default from_number aget_ctor)
        | AIexpr (base, index) ->
          AIexpr (fn base from_container (cget_ctor Number),
                  fn index Utils.identity eget_ctor)
        | Length c -> Length (fn c from_container (cget_ctor Unknown))
        | Abinop (op, left, right) -> 
          Abinop (op, 
                  fn left from_number aget_ctor,
                  fn right from_number aget_ctor)
        | _ -> e in 
      let bfn e = match e with 
        | CustomBoolean (s, kvlist, salt) -> 
          CustomBoolean (s, List.map (fun (k, v) ->
            (k, fn v Utils.identity eget_ctor)) kvlist, salt)
        | CoalesceBoolean (attempt, default) -> 
          CoalesceBoolean (fn attempt from_boolean bget_ctor,
                           fn default from_boolean bget_ctor)
        | BIexpr (base, index) -> 
          BIexpr (fn base from_container (cget_ctor Boolean),
                  fn index Utils.identity eget_ctor)
        | Not e -> Not (fn e from_boolean bget_ctor)
        | Equals (e1, e2) ->
          Equals (fn e1 Utils.identity eget_ctor, 
                  fn e2 Utils.identity eget_ctor)
        | BinBinOp (op, e1, e2) -> 
          BinBinOp (op, fn e1 from_boolean bget_ctor, 
                        fn e2 from_boolean bget_ctor)
        | BinStrOp (op, e1, e2) -> 
          BinStrOp (op, fn e1 from_string sget_ctor, 
                        fn e2 from_string sget_ctor)
        | BinCtrOp (op, e1, e2) -> 
          BinCtrOp (op, fn e1 from_container (cget_ctor Unknown), 
                        fn e2 from_container (cget_ctor Unknown))
        | BinNumOp (op, e1, e2) -> 
          BinNumOp (op, fn e1 from_number aget_ctor, 
                        fn e2 from_number aget_ctor)
        | _ -> e 
        in 
      let cfn e = match e with 
        | CustomContainer (s, kvlist, t, salt) ->
          CustomContainer (s, List.map (fun (k, v) ->
            (k, fn v Utils.identity eget_ctor)) kvlist, t, salt)
        | CoalesceContainer (attempt, default) ->
          (* TODO: grab the codomain types. *)
          let t = Unknown in 
          CoalesceContainer (fn attempt from_container (cget_ctor t),
                             fn default from_container (cget_ctor t))
        | CIexpr (base, index) ->
          CIexpr (fn base from_container (cget_ctor Container),
                  fn index Utils.identity eget_ctor)
        | Range (min, max) ->
          Range (fn min from_number aget_ctor, fn max from_number aget_ctor)
        | _ -> e in 
      let sfn e = match e with 
        | CustomString (s, kvlist, salt) ->
          CustomString (s, List.map (fun (k, v) ->
            (k, fn v Utils.identity eget_ctor)) kvlist, salt)
        | CoalesceString (attempt, default) ->
          CoalesceString (fn attempt from_string sget_ctor,
                          fn default from_string sget_ctor)
        | SIexpr (base, index) ->
          SIexpr (fn base from_container (cget_ctor String), 
                  fn index Utils.identity eget_ctor)
        | _ -> e in 
      let program = 
        (* lift functions from all guards and return statements *)
        tree_rewrite ~breadth:true ~astfn program 
        |> tree_rewrite ~breadth:false ~astfn:ast_inject
        (* linearize expressions *)
        |> tree_rewrite ~breadth:false ~efn ~afn ~bfn ~cfn ~sfn 
        (* inject linearized expressions *)
        |> tree_rewrite ~breadth:false ~astfn:ast_inject 
        (* cleans up guards *)
        |> tree_rewrite ~breadth:false ~astfn:lift_rel_guard 
        in 
      (config, program)

    let linearize_steady ~varid (config, program) = 
      let update = ref true in 
      let program = ref program in 
      let config = ref config in 
      while !update do 
        let (c', p') = linearize_fn_app varid (!config, !program) 
                      |> minimize_program in 
        if !program = p'
        then update := false
        else (program := p'; config := c')
      done;
      (!config, !program)
    
    let add_default_guard ~skipid (config, Program p) = 
      let has_default (glist : ast_node list) =
        match List.hd (List.rev glist) with
        | Guard (POBoolean true) -> true
        | _ -> false in 
      let rec helper n = match n with 
        | Cond conds ->
          let (guards, cons) = List.split conds in
          let has_default = has_default guards in 
          let guards' = 
            List.map (function Guard g -> g | _ -> assert false) guards	
            (* Each guard needs to be the current value /\ negation of prior 
            disjunction. *)
            |> List.fold_left (fun (glist, disj) g ->
                    (glist @ [Guard (BinBinOp (And, g, Not disj))], 
                  BinBinOp (Or, g, disj)))
                ([],  POBoolean false)
            |> (fun (glist, disj) -> if has_default then glist 
                else glist @ 
                [Guard (BinBinOp (And, POBoolean true, Not disj))]) in 
        let cons' = List.map helper cons in 
        Cond (List.combine guards' 
          (match List.length guards', List.length cons' with
          | n, m when n = m -> cons'
          | n, m when n = m + 1 -> cons' @ [Skip (Po_counters.skipid ()) ]
          | _ -> assert false))
        | Seq seqs -> Seq (List.map helper seqs |> flatten_seqs)
        | e -> e in 
      (config, Program (helper p))

    let get_codomain_values (e : po_cexpr) : po_expr list option = match e with
      | POMap (_, m) -> Some (POMap_.bindings m |> List.map snd)
      | POArray (_, arr) -> Some arr
      | _ -> None

    let lift_unit_exprs ~varid ((config : POConfig.typequals), program) = 
      let swap_unit e unitstring = 
        let unitid = UnitR unitstring in 
        match e with 
        | CustomExpr (s, kvlist, Some {salt; unit_arg}) ->
          CustomExpr (s, kvlist, Some {salt; unit_value=unitid; unit_arg})
        | RandomVar (weights, choices, unit_value, salt) ->
          RandomVar (weights, choices, unitid    , salt)
        | Aexpr (RandomNumber    (weights, choices, unit_value, salt)) ->
          Aexpr (RandomNumber    (weights, choices, unitid    , salt))
        | Bexpr (RandomBoolean   (weights, choices, unit_value, salt)) ->
          Bexpr (RandomBoolean   (weights, choices, unitid    , salt))
        | Cexpr (RandomContainer (weights, choices, unit_value, salt)) ->
          Cexpr (RandomContainer (weights, choices, unitid    , salt))
        | Sexpr (RandomString    (weights, choices, unit_value, salt)) ->
          Sexpr (RandomString    (weights, choices, unitid    , salt))
        | _ -> assert false 
        in
      let new_vars = ref [] in 
      let efn e = match e with 
        | CustomExpr (_, _, Some {unit_value}) -> begin 
          match unit_value with 
            | UExpr ue -> 
              let newid = varid () in 
              new_vars := (newid, ue)::!(new_vars); 
              swap_unit e newid 
            | _ -> e end 
        | RandomVar (_, _, unit_value, _) -> begin 
          match unit_value with 
            | UExpr ue -> 
              let newid = varid () in 
              new_vars := (newid, ue)::!(new_vars); 
              swap_unit e newid
            | _ -> e end
        | _ -> e in 
      let afn e = match e with 
        | RandomNumber (_, _, unit_value, _) -> begin 
          match unit_value with 
            | UExpr ue -> 
              let newid = varid () in 
              new_vars := (newid, ue)::!(new_vars); 
              swap_unit (Aexpr e) newid |> to_number
            | _ -> e end
        | _ -> e in    
      let bfn e = match e with 
        | RandomBoolean (_, _, unit_value, _) -> begin 
          match unit_value with 
            | UExpr ue -> 
              let newid = varid () in 
              new_vars := (newid, ue)::!(new_vars); 
              swap_unit (Bexpr e) newid |> to_boolean
            | _ -> e end
        | _ -> e in    
      let (Program stmts) = tree_rewrite ~efn ~afn ~bfn program in 
      let new_assignments = List.map (fun (id, e) -> 
          Assignment (Synth, id, 1, e)
        ) !new_vars in   
      let prog : program = if List.length new_assignments > 0
        then Program (Seq (new_assignments @ [stmts] |> flatten_seqs)) 
        else Program stmts in 
      let config : POConfig.typequals = 
        List.fold_left 
          (fun (config : POConfig.typequals) (id, e) -> 

            let refs : string list  = Po_aux.get_node_vars (Expr e)
              |> Config.Params.elements
              |> List.map fst in 

            let has_high_card : bool = Utils.exists (fun s -> 
                POConfig.get_cardinality s config = Some Config.High
              ) refs in 

            let cfg : POConfig.config = POConfig.make_config 
              ~card:(if has_high_card then Config.High else Config.Low) () in 

            (POConfig.update_config id cfg config)
        ) config !new_vars in 
      (config, prog)

    let lift_random_variables ~varid (config, program) = 
      let module RandomVars = Map.Make(struct 
          type t = Po_syntax.po_sexpr 
          let compare s1 s2 = String.compare 
            (Po_format.string_of_expr (Sexpr s1))
            (Po_format.string_of_expr (Sexpr s2))
        end) in 
      let embedded = ref RandomVars.empty in 
      let direct = ref RandomVars.empty in 
      let add_assignments n = 
        let vars : (string * int) list = 
          Po_aux.get_node_vars n
          |> Config.Params.filter (fun (p, _) -> 
                RandomVars.mem (POString p) !embedded) 
          |> Config.Params.elements in 
        (* Adds definitions for random variables. *)
        let defs = List.map (fun ((l : string), (i : int)) -> 
            assert (i = 1);
            Assignment (Synth, l, 1, RandomVars.find (POString l) !embedded))
          vars in 
        (* Removes these random variables from being tracked, since we don't 
        want to define them twice. *)
        embedded := List.fold_left 
          (fun m (l, _) -> RandomVars.remove (POString l) m) !embedded vars; 
        Seq (defs @ [n] |> flatten_seqs) in 
      let open Po_syntax in 
      let lift_random (type t) (s : po_sexpr) (e : t) convert_fn get_ctor  = 
        if RandomVars.mem s !direct
        then e 
        else begin  
          match s with 
            | POString s' when s' <> empty_string && s' <> "NULL" -> 
              embedded := RandomVars.add s (convert_fn e) !embedded;
              get_ctor Synth Random s' 1 
            | _ -> 
              let s' = varid () in 
              embedded := RandomVars.add (POString s') (convert_fn e) !embedded;
              get_ctor Synth Random s' 1 
        end in
      let astfn n = match n with 
        | Assignment (_, s, _, e) when Po_aux.is_random_variable e -> 
          direct := RandomVars.add (POString s) e !direct; n
        | _ -> n in 
      let efn e = match e with 
        | CustomExpr (_, _, Some {salt}) 
        | RandomVar (_, _, _, salt) -> 
          lift_random salt e Utils.identity eget_ctor
        | _ -> e in
      let afn e = match e with 
        | CustomNumber (_, _, Some {salt})
        | RandomNumber (_, _, _, salt) -> 
          lift_random salt e from_number aget_ctor
        | _ -> e in 
      let bfn e = match e with 
        | CustomBoolean (_, _, Some {salt})
        | RandomBoolean (_, _, _, salt) -> 
          lift_random salt e from_boolean bget_ctor
        | _ -> e in 
      let cfn e = match e with 
        | CustomContainer (_, _, t, Some {salt}) -> 
          lift_random salt e from_container (cget_ctor t)
        | RandomContainer (_, choices, _, salt) -> 
          (* later get codomain on choices. *)
          lift_random salt e from_container (cget_ctor Unknown)
        | _ -> e in 
      let sfn e = match e with 
        | CustomString (_, _, Some {salt})
        | RandomString (_, _, _, salt) -> 
          lift_random salt e from_string sget_ctor
        | _ -> e in 
      (config, tree_rewrite ~breadth:false ~astfn program 
              |> tree_rewrite ~breadth:false ~astfn:add_assignments 
                  ~efn ~afn ~bfn ~cfn ~sfn)

    let infer_container_codomains env types (config, program) = 
      (* track container codomains in the type environment. 
         do this by prepending a unique prefix to the variable name. *)
      let codomain_prefix = "^cd_" in 
      let add_codomain name t = 
        Po_aux.add_type types (codomain_prefix ^ name) t in
      let lookup_codomain e name = 
        Po_aux.resolve_type e types (codomain_prefix ^ name) in 
      let astfn n = match n with 
        | Assignment (o, s, i, 
          (Iexpr (GetContainer (o', m', s', i', Unknown), index) as e)) ->
          env := Po_env.add ~o (s, i) e !env;
          let t = Po_aux.resolve_type e types s in 
          add_codomain s' t;
          Assignment (o, s, i, 
            let base = GetContainer (o', m', s', i', t) in 
            match t with 
            | Number -> Aexpr (AIexpr (base, index))
            | Boolean -> Bexpr (BIexpr (base, index))
            | Container -> Cexpr (CIexpr (base, index))
            | String -> Sexpr (SIexpr (base, index))
            | Unknown -> Iexpr (base, index)
          )
        | Assignment (o, s, i, 
            (Cexpr (CustomContainer (name, kvlist, Unknown, salt)) as e)) ->
          let t = lookup_codomain e s in 
          Assignment (o, s, i, 
            Cexpr (CustomContainer (name, kvlist, t, salt)))
        | Assignment (o, s, i, e) -> 
          env := Po_env.add ~o (s, i) e !env; n
        | _ -> n in 
      let open Po_syntax in 
      let afn e = match e with 
        | AIexpr (GetContainer (o, m, s, i, t), index) when t <> Number ->
          add_codomain s Number;
          AIexpr (GetContainer (o, m, s, i, Number), index)
        | RandomNumber (weights, GetContainer (o, m, s, i, Unknown), 
            unitr, salt) -> 
          add_codomain s Number;
          RandomNumber (weights, 
            GetContainer (o, m, s, i, Number), unitr, salt)
        | _ -> e in 
      let bfn e = match e with 
        | BIexpr (GetContainer (o, m, s, i, t), index) when t <> Boolean ->
          BIexpr (GetContainer (o, m, s, i, Boolean), index)
        | _ -> e in 
      let cfn e = match e with 
        | POArray (Unknown, arr) -> 
          POArray (Po_aux.get_type_of_list arr, arr)
        | POMap (Unknown, m) -> 
          POMap (POMap_.bindings m |> List.map snd |> Po_aux.get_type_of_list, m)
        | GetContainer (o, m, s, i, Unknown) ->
          let codom = lookup_codomain (Cexpr e) s in 
          if codom <> Unknown 
          then GetContainer (o, m, s, i, codom)
          else if Po_env.mem (s, i) !env 
          then 
            let e' = Po_env.find (s, i) !env 
                     |> (fun e -> if Po_aux.is_phi e then e 
                          else e |> to_container |> from_container) in 
            GetContainer (o, m, s, i, Po_aux.get_codomain ~env:!env e')
          else e
        | CIexpr (GetContainer (o, m, s, i, t), index) when t <> Container ->
          CIexpr (GetContainer (o, m, s, i, Container), index)
        | RandomContainer (w, GetContainer (o, m, s, i, Unknown), u, slt) ->
          RandomContainer (w, GetContainer (o, m, s, i, Container), u, slt)
        | _ -> e in 
      let sfn e = match e with 
        | SIexpr (GetContainer (o, m, s, i, t), index) when t <> String ->
          add_codomain s String;
          SIexpr (GetContainer (o, m, s, i, String), index)
        | RandomString (w, GetContainer (o, m, s, i, Unknown), u, slt) ->
          add_codomain s String;
          RandomString (w, GetContainer (o, m, s, i, String), u, slt)
        | _ -> e in 
      (config, tree_rewrite ~astfn ~afn ~bfn ~cfn ~sfn program)

    let promote_unclassified_to_random (config, program) = 
      let module RandomVars = Set.Make(String) in 
      let random_vars = ref RandomVars.empty in 
      let astfn n = match n with 
        | Assignment (_, s, _, CustomExpr             (_, _,    Some _)) 
        | Assignment (_, s, _, Aexpr (CustomNumber    (_, _,    Some _)))
        | Assignment (_, s, _, Bexpr (CustomBoolean   (_, _,    Some _)))
        | Assignment (_, s, _, Cexpr (CustomContainer (_, _, _, Some _))) 
        | Assignment (_, s, _, Sexpr (CustomString    (_, _,    Some _))) 
        | Assignment (_, s, _, RandomVar _)
          -> random_vars := RandomVars.add s !random_vars; n
        | _ -> n in 
      let efn e = match e with 
        | Get (o, Unclassified, s, i) 
          when RandomVars.mem s !random_vars -> Get (o, Random, s, i)
        | _ -> e in 
      let afn e = match e with 
        | GetNumber (o, Unclassified, s, i) 
          when RandomVars.mem s !random_vars -> GetNumber (o, Random, s, i)
        | _ -> e in 
      let bfn e = match e with 
        | GetBoolean (o, Unclassified, s, i) 
          when RandomVars.mem s !random_vars -> GetBoolean (o, Random, s, i)
        | _ -> e in 
      let cfn e = match e with 
        | GetContainer (o, Unclassified, s, i, t) 
          when RandomVars.mem s !random_vars -> GetContainer (o, Delay, s, i, t)
        | _ -> e in 
      let sfn e = match e with 
        | GetString (o, Unclassified, s, i) 
          when RandomVars.mem s !random_vars -> GetString (o, Delay, s, i)
        | _ -> e in 
      (config, tree_rewrite ~astfn ~efn ~afn ~bfn ~cfn ~sfn program)

    let promote_unclassified_to_delay (config, program) = 
      let efn e = match e with 
        | Get (o, Unclassified, s, i) -> Get (o, Delay, s, i)
        | _ -> e in 
      let afn e = match e with 
        | GetNumber (o, Unclassified, s, i) -> GetNumber (o, Delay, s, i)
        | _ -> e in 
      let bfn e = match e with 
        | GetBoolean (o, Unclassified, s, i) -> GetBoolean (o, Delay, s, i)
        | _ -> e in 
      let cfn e = match e with 
        | GetContainer (o, Unclassified, s, i, t) -> 
          GetContainer (o, Delay, s, i, t)
        | _ -> e in 
      let sfn e = match e with 
        | GetString (o, Unclassified, s, i) -> GetString (o, Delay, s, i)
        | _ -> e in 
      (config, tree_rewrite ~efn ~afn ~bfn ~cfn ~sfn program)

    let minimize_seqs ~skipid (config, program) = 
      let astfn n = match n with 
        | Seq [] -> Skip (skipid ())
        | Seq [n'] -> n'
        | Seq seqs -> Seq (flatten_seqs seqs)
        | _ -> n in 
      (config, tree_rewrite ~astfn program)

    let resolve_type e types name = 
      let open Po_syntax in 
      let rec one_of ?(seen=[]) looking_for base = match base with 
      | [] -> seen
      | h::t when List.mem h looking_for && (not (List.mem h seen)) -> 
        one_of looking_for t ~seen:(h::seen)
      | _::t -> one_of looking_for t ~seen in 
      if Po_aux.Types.mem name !types 
      then 
        let these_types = Po_aux.Types.find name !types in 
        Logger.print_debug __LINE__ "types for %s: [%s]" name 
          (Utils.join "; " Po_syntax.show_base_type these_types);
        match one_of [String; Container; Number] these_types with 
        | [] -> begin match one_of [Boolean] these_types with 
            | [] -> Unknown
            | [t] -> t 
            | _ -> assert false 
          end
        | [t] -> t
        | [Number; Boolean]
        | [Boolean; Number] -> Boolean 
        (* | _ -> Unknown *)
        | t1::t2::_ -> raise (type_error ~expected:t1 ~found:t2 e) 
      else Unknown 

    let remove_type name types t = 
      let removed = Po_aux.Types.find name !types 
               |> List.filter ((<>) t) in 
      types := Po_aux.Types.add name removed !types 

    let specialize_types env types (config, program) = 
      let open Po_syntax in 
      let specialize_random_var t2 weights choices u salt = match t2 with 
        | Number -> Aexpr (RandomNumber (weights, choices, u, salt))
        | Boolean -> Bexpr (RandomBoolean (weights, choices, u, salt))
        | Container -> Cexpr (RandomContainer (weights, choices, u, salt))
        | String -> Sexpr (RandomString (weights, choices, u, salt))
        | Unknown -> RandomVar (weights, choices, u, salt) in 
      let specialize_bool b o m s i = 
        (* it's clearly being used as a bool. *)
        Po_aux.add_type types s Boolean;
        begin match Po_aux.resolve_type (Bexpr b) types s with 
          | Number -> Not (BinNumOp (AEquals, 
              PONumber Oratio.zero, 
              GetNumber (o, m, s, i)))
          | Container -> Not (BinNumOp (AEquals,
              PONumber Oratio.zero, 
              Length (GetContainer (o, m, s, i, Unknown))))
          | String -> Not (BinStrOp (SEquals,
              po_empty_string, GetString (o, m, s, i)))
          | Unknown | Boolean -> GetBoolean (o, m, s, i) 
        end in 
      let astfn n = match n with 
        | Assignment (o, s, i, e) ->
          env := Po_env.add ~o (s, i) e !env ; 
          if Po_aux.is_phi e 
          then n 
          else 
            let t = Po_aux.get_expression_type e in 
            (Po_aux.add_type types s t; n)
        | _ -> n in 
      let efn e = match e with 
        | Get (o, m, s, i) -> 
          if Po_env.mem (s, i) !env 
          then begin 
            let e' = Po_env.find (s, i) !env in 
            (*match Po_aux.get_expression_type e' with *)
            match resolve_type e types s with 
            | Number -> Aexpr (GetNumber (o, m, s, i))
            | Boolean -> Bexpr (GetBoolean (o, m, s, i))
            | Container -> 
              Cexpr (GetContainer (o, m, s, i, Po_aux.get_codomain ~env:!env e'))
            | String -> Sexpr (GetString (o, m, s, i))
            | Unknown -> e end
          else begin 
            let open POCfg in 
            let cfg = get_config s config in 
            match cfg.domain with 
              | Var Number -> Aexpr (GetNumber (o, m, s, i))
              | Var Boolean -> Bexpr (GetBoolean (o, m, s, i))
              | Var Container -> Cexpr (GetContainer (o, m, s, i, Unknown))
              | Var String -> Sexpr (GetString (o, m, s, i))
              | _ -> e 
            end
        | Iexpr (POArray _ as base, Get (o, m, s, i)) ->
          Iexpr (base, Aexpr (GetNumber (o, m, s, i)))
        | Iexpr (POArray (t, _) as base, index)
        | Iexpr (POMap (t, _) as base, index) ->
          begin match t with 
            | Number -> Aexpr (AIexpr (base, index))
            | Boolean -> Bexpr (BIexpr (base, index))
            | Container -> Cexpr (CIexpr (base, index))
            | String -> Sexpr (SIexpr (base, index))
            | Unknown -> e
          end 
        (* | Iexpr (base, Get (o, m, s, i) as index) ->  *)
        | RandomVar (GetContainer (o, m, s, i, t1), choices, u, salt) ->
          let t2 = Po_aux.get_codomain ~env:!env (Cexpr choices) in 
          (*Printf.printf "(1) codomain type for %s: %s\n" salt (Basetypes.string_of_base_type t2);*)
          let t1 = (if t1 = Unknown || t1 = Number 
            then Number else assert false) in 
          specialize_random_var t2 (GetContainer (o, m, s, i, t1)) choices u salt 
        | RandomVar (weights, choices, u, salt) ->
          let t = Po_aux.get_codomain ~env:!env (Cexpr choices) in 
          (*Printf.printf "(2) codomain type for %s: %s\n" salt (Basetypes.string_of_base_type t);*)
          specialize_random_var t weights choices u salt
        | Coalesce (e1, Aexpr e2) -> Aexpr (CoalesceNumber (to_number e1, e2))
        | Coalesce (e1, Bexpr e2) -> Bexpr (CoalesceBoolean (to_boolean e1, e2))
        | Phi (Unknown, name, ints) -> 
          Phi (resolve_type e types name, name, ints)
        | _ -> e in
      let afn e = match e with 
        | AIexpr (POArray _ as base, Get (o, m, s, i)) ->
          AIexpr (base, Aexpr (GetNumber (o, m, s, i)))
        | GetNumber (_, _, s, _) -> 
          Po_aux.add_type types s Number; 
          ignore (resolve_type (Aexpr e) types s); e
        | _ -> e in 
      let bfn e = match e with 
        | BIexpr (POArray _ as base, Get (o, m, s, i)) ->
          BIexpr (base, Aexpr (GetNumber (o, m, s, i)))
        | GetBoolean (o, m, s, i) -> 
          specialize_bool e o m s i 
        | Equals (e1, e2) -> 
          let t1 = Po_aux.get_expression_type e1 in 
          let t2 = Po_aux.get_expression_type e2 in 
          begin match t1, t2 with 
            | Boolean, _ | _, Boolean ->
              BinBinOp (BEquals, to_boolean e1, to_boolean e2)
            | String, _  | _, String -> 
              BinStrOp (SEquals, to_string e1, to_string e2)
            | Number, _ | _, Number ->
              BinNumOp (AEquals, to_number e1, to_number e2)
            | Container, _ | _, Container ->
              BinCtrOp (CEquals, to_container e1, to_container e2)
            | _ -> e
          end
        | _ -> e in 
      let cfn e = match e with 
        | CIexpr (POArray _ as base, Get (o, m, s, i)) ->
          CIexpr (base, Aexpr (GetNumber (o, m, s, i)))
        | CIexpr (GetContainer (o, m, s, i, t), index) ->
          let get_base = GetContainer (o, m, s, i, Container) in 
          Po_aux.add_type types s Container;
          let e = if Po_env.mem (s, i) !env 
                  then 
                    let e' = Po_env.find (s, i) !env in 
                    if Po_aux.is_phi e'
                    then get_base
                    else to_container e'
                  else get_base in 
          env := Po_env.add ~o (s, i) (Cexpr e) !env;
          CIexpr (get_base, index)
        | GetContainer (o, m, s, i, t) -> 
          Po_aux.add_type types s Container; 
          ignore (resolve_type (Cexpr e) types s); 
          e
        | _ -> e in 
      let sfn e = match e with 
        | SIexpr (POArray _ as base, Get (o, m, s, i)) ->
          SIexpr (base, Aexpr (GetNumber (o, m, s, i)))
        | GetString (_, _, s, _) -> 
          Po_aux.add_type types s String; 
          ignore (resolve_type (Sexpr e) types s); e
        | _ -> e in 
      let astfnt n = match n with 
        | Return (GetBoolean (o, m, s, i) as b) ->
          let t = resolve_type (Bexpr b) types s in 
          Logger.print_debug __LINE__ 
            "%s_%d has type %s" s i (Po_syntax.string_of_base_type t);
          begin match t with 
            | Number -> Return (Not (BinNumOp (AEquals, 
                PONumber Oratio.zero, 
                GetNumber (o, m, s, i))))
            | Container -> Return (Not (BinNumOp (AEquals,
                PONumber Oratio.zero, 
                Length (GetContainer (o, m, s, i,Unknown)))))
            | String -> Return (Not (BinStrOp (SEquals,
                po_empty_string, GetString (o, m, s, i))))
            | Unknown | Boolean -> n
          end
        | Assignment (o, s, i, e) -> 
          if Po_aux.Types.mem s !types && not (Po_aux.is_phi e)
          then 
            let found_type = Po_aux.resolve_type e types s in begin 
            Logger.print_debug __LINE__ 
              "Found prior match for assignment %s in the types dictionary (%s)"
              (Po_format.string_of_program (Program n))
              (Po_syntax.show_base_type found_type)
              ;
            Assignment (o, s, i, match found_type with 
                | Number -> Aexpr (to_number e)
                | Boolean -> Bexpr (to_boolean e)
                | Container -> Cexpr (to_container e)
                | String -> Sexpr (to_string e)
                | Unknown -> e)
            end
          else n
        | _ -> n in 
      Logger.print_debug __LINE__
        "Specializing %s"
        (Po_syntax.show_program program);
      let tree = 
        tree_rewrite ~breadth:false ~astfn ~efn ~afn ~bfn ~cfn ~sfn program 
        (* |> tree_rewrite ~breadth:false ~astfn ~efn ~afn ~bfn ~cfn ~sfn   *)
        |> tree_rewrite ~breadth:true ~astfn:astfnt 
        in 
      (config, tree)

    let update_external_to_random (config, program) = 
      let config = ref config in 
      let open POCfg in 
      let open Po_syntax in 
      let set_rand_var (type s) o m s i t err_cond ctor : s =
        if is_random s !config 
        then 
          let cfg = get_config s !config in 
          let domain = match cfg.domain with 
            | FnArg lst when List.length lst > 0 -> 
              raise (Config.make_config_format_err ~field:"domain" 
                ~msg:"Expecting domain to be a list of length 1 for values.")
            | FnArg _ -> Unknown
            | Var domain -> domain  in 
          if err_cond domain 
          then 
            raise (Parse.make_coersion_err s ~t_to:t ~t_from:domain)
          else 
            if domain = Unknown
            then config := update_config s (update_domain (Var t) cfg) !config;
            ctor o Random s i 
        else ctor o m s i in 
      let err_cond_t t1 t2 = t2 <> Unknown && t2 <> t1 in  
      let afn e = match e with 
        | GetNumber (o, m, s, i) ->
          set_rand_var o m s i Number (err_cond_t Number) Po_eval.get_num_ctor
        | _ -> e in 
      let bfn e = match e with 
        | GetBoolean (o, m, s, i) ->
          set_rand_var o m s i Boolean (err_cond_t Boolean) Po_eval.get_bool_ctor 
        | _ -> e in 
      let cfn e = match e with 
        | GetContainer (o, m, s, i, t) ->
          set_rand_var o m s i Container (err_cond_t Container) 
            (Po_eval.get_ctr_ctor t) 
        | _ -> e in 
      let sfn e = match e with           
        | GetString (o, m, s, i) ->
          set_rand_var o m s i String (err_cond_t String) Po_eval.get_str_ctor 
        | _ -> e in 
      let efn e = match e with 
        | Get (o, m, s, i) ->
          set_rand_var o m s i Unknown (err_cond_t Unknown) Po_eval.get_ctor 
        | _ -> e in 
      (!config, tree_rewrite ~efn ~afn ~bfn ~cfn ~sfn program)

    let specialize_steady ~varid (config, program) = 
      let update = ref true in 
      let program = ref program in 
      let config = ref config in 
      let env = ref Po_env.empty in 
      let types = ref (
        POCfg.bindings !config
        |> List.fold_left (fun types (k, cfg) ->
            let open POCfg in 
            match cfg.domain with 
            | POCfg.Var bt -> Po_aux.Types.add k [bt] types
            | _ -> types)
          Po_aux.Types.empty
      ) in 
      while !update do 
        let (c, p) = infer_container_codomains env types (!config, !program)
                    |> specialize_types env types  in 
        if p = !program 
        then update :=false 
        else (program := p; config := c)
      done;
      (!config, !program)

    let explicit_return_conversion ~varid (config, program) = 
      (* we will only run into this problem when a return's argument is 
        a get that is a number, acting like a boolean. *)
      let astfn n = match n with 
        | Return (GetBoolean (o, m, s, i)) ->
          Logger.print_debug __LINE__ "%s_%d var type: %s\n" s i 
            (Po_aux.infer_var_type (s, i) program 
            |> Po_syntax.string_of_base_type);
          let open Po_syntax in 
          begin match Po_aux.infer_var_type (s, i) program with 
            | Number -> begin 
                let s' = varid () in 
                let i' = 1 in 
                Seq [
                  Assignment (Synth, s', i',
                    Bexpr (Not (BinNumOp (AEquals, 
                      PONumber Oratio.zero,
                      GetNumber (o, m, s, i)))));
                  Return (GetBoolean (Synth, Unclassified, s', i'))
                ]
              end 
            | _ -> n 
          end 
        | Return e -> 
          Logger.print_debug __LINE__
            "No conversion for return expression: [%s] (%s)"
              (Po_format.string_of_expr (Bexpr e)) 
              (Po_format.ast_string_of_expr (Bexpr e));
          n 
        | _ -> n in 
      (config, tree_rewrite ~breadth:false ~astfn program)

    let update_salts (config, program) = 
      let update_rand_info rand_info label : rand_info option = 
        let {unit_arg; unit_value} = rand_info in 
        let salt = POString label in 
        Some {salt; unit_arg; unit_value} in 
      let custom_ctor e fname kvlist rand_info : po_expr = match e with 
        | CustomExpr _ -> CustomExpr (fname, kvlist, rand_info)
        | Aexpr (CustomNumber _) -> 
          Aexpr (CustomNumber (fname, kvlist, rand_info)) 
        | Bexpr (CustomBoolean _) -> 
          Bexpr (CustomBoolean (fname, kvlist, rand_info))
        | Cexpr (CustomContainer (_, _, t, _)) -> 
          Cexpr (CustomContainer (fname, kvlist, t, rand_info))
        | Sexpr (CustomString _) -> 
          Sexpr (CustomString (fname, kvlist, rand_info)) 
        | _ -> assert false in 
      let astfn n = match n with 
      | Assignment (o, label, i, (CustomExpr (fn, kvlist, Some rand_info) as e))
        -> begin 
            if rand_info.salt = po_empty_string || 
               rand_info.salt = POString "NULL" 
            then Assignment (o, label, i, 
              update_rand_info rand_info label
              |> custom_ctor e fn kvlist) 
            else n 
        end
      | _ -> n in 
      (config, tree_rewrite ~breadth:false ~astfn program)

    let normalize config program =
      (* reset !varid. this ensures idempotency. *)
      reset_varid ();
      reset_skipid ();
      let varid = Po_counters.thread_safe_copy 
        ~prefix:Po_counters.pseudo_prefix "varid" in 
      let skipid = Po_counters.skipid in 
      let printfn step (config, program) = 
        Logger.print_debug __LINE__ "REWRITE RULE: %s\n%s" 
          step (Po_format.string_of_program ~show_index:true program);
        (config, program) in 
      (* reset env; also ensures idempotency *)
      (*Log.debug "%s" (Po_format.string_of_program ~show_index:true program);*)
      (* Po_parse._env := Po_env.empty; *)
      (config, program)
      |> update_salts 
      |> printfn "update_salts"
      |> constant_min_steady
      |> printfn "constant_min_steady 1"
      |> specialize_steady ~varid
      |> printfn "specialize_steady 1"
      |> lift_random_variables ~varid
      |> printfn "lift_random_variables"
      |> minimize_seqs ~skipid
      |> printfn "minimize_seqs 1"
      (* |> explicit_return_conversion ~varid
      |> printfn "explicit_return_conversion"  *)
      |> linearize_steady ~varid
      |> printfn "linearize_steady"
      (* Need to add default guard after linearization or we get too many 
      repetitions of expressions. *)
      |> add_default_guard ~skipid
      |> printfn "add_default_guard"
      |> update_external_to_random
      |> printfn "update_external_to_random"
      |> promote_unclassified_to_random
      |> printfn "promote_unclassified_to_random"
      |> promote_unclassified_to_delay
      |> printfn "promote_unclassified_to_delay"
      |> minimize_seqs ~skipid
      |> printfn "minimize_seqs 2"
      |> constant_min_steady
      |> printfn "constant_min_steady 2"
      |> specialize_steady ~varid
      |> printfn "specialize_steady 2"
      |> lift_unit_exprs ~varid
      |> printfn "lift_unit_exprs"
end
