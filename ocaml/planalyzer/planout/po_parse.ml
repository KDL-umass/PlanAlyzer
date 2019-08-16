(** Dependencies:
    - po_aux 
    - po_env
    - po_kwd
    - po_syntax 
*)

module Logger = Logging.Make (struct 
    let file = __FILE__
    let phase = Logging.Normalize
  end)

module type Parse = sig
    open Po_syntax

    module POConfig : Config.Config with type basetype = base_type
    type typequals 
    exception MissingUnitError of string * string list
    exception Malformed_unit of po_expr
    exception Malformed_json of string 
    exception CodomainMismatch of Po_kwd.kwd * base_type * Yojson.Basic.json
    exception PlanOut_syntax of po_expr * base_type 
    val make_coersion_err : string -> t_from:base_type -> t_to:base_type -> exn
    val make_missing_unit_err : fn:string -> unit:string -> exn
    val exec_po_compiler : string -> string 
    val make_program : typequals -> Yojson.Basic.json -> Po_syntax.program 
end

module MakeParse(
  POCfg : Config.Config with type basetype = Po_syntax.base_type
) = struct

  include Po_syntax

  open Printf
  open Config 

  module POConfig = POCfg
  type typequals = POCfg.typequals
  type env_key = Po_env.env_key

  module YBU = Yojson.Basic.Util
  module YB = Yojson.Basic

  exception Bad_salt_source of po_expr
  exception PlanOut_syntax of po_expr * base_type 
  exception Malformed_json of string 
  exception NYI of string
  exception GuardErr of po_expr
  exception CodomainMismatch of Po_kwd.kwd * base_type * YB.json
  exception InvalidUnitIdentifier of string
  exception UnsoundTypeCoersion of string * base_type * base_type
  exception MissingUnitError of string * string list
  exception CustomMissingUnitError of string * string 
  exception Malformed_unit of po_expr
  exception DataFlowDeterminism of po_expr 

  let make_coersion_err name ~t_from ~t_to =  
    UnsoundTypeCoersion (name, t_from, t_to)

  let make_missing_unit_err ~fn ~unit = 
    CustomMissingUnitError (fn, unit)

  let empty_string = ""
  let po_empty_string = POString empty_string

  (* let _env = ref Po_env.empty  *)
  module IndexMap = Map.Make(String)
  let global_max_index_map = ref IndexMap.empty
  let find_max_index s im = 
    if IndexMap.mem s im 
    then IndexMap.find s im 
    else 0
  module OriginMap = Po_env.Env.Delta 
  let global_origin_map = ref OriginMap.empty 
  let find_origin k om = 
    if OriginMap.mem k om 
    then OriginMap.find k om 
    else ExtSource

  let make_get (type t) s im (fn : 'a -> 'b -> 'c -> 'd -> t) = 
    let i = find_max_index s im in
    let o = find_origin (s, i) !global_origin_map in  
    let m = if i = 0 then External else Unclassified in 
    fn o m s i

  let exec_po_compiler (file_content : string) : string =
    (* Print content to temp file. *)
    try
      let (fname, out) = Core.Filename.open_temp_file "script" "po" in 
      Core.Out_channel.output_string out file_content; 
      Core.Out_channel.flush out;
      let stdout = Core.Unix.open_process_in ("node $PLANOUT " ^ fname) in 
      Core.In_channel.input_all stdout
    with _ -> failwith "oops"

  let rec ast_contains_kv (k : string) (v : string) ast : bool =
    try 
      (match YBU.member k ast with
      | `String s -> if s = v then true else false
      | _ -> Utils.exists Utils.identity (List.map (ast_contains_kv k v) 
            (YBU.to_assoc ast |> List.map snd)))
    with YBU.Type_error _ -> false 

  let split_id s =
    match String.compare (String.sub s (String.length s - 2) 2) "id" with
    | 0 -> [String.sub s 0 (String.length s - 2); "id"]
    | _ -> [s]

  let get_salt (e: po_expr) : po_sexpr =
    match e with
    | Aexpr (RandomNumber (_, _, _, s)) -> s
    | Bexpr (RandomBoolean (_, _, _, s)) -> s
    | Cexpr (RandomContainer (_, _, _, s)) -> s
    | Sexpr (RandomString (_, _, _, s)) -> s
    | _ -> raise (Bad_salt_source e)

  let get_op_kwd js = 
    match YBU.filter_member Po_kwd.op [js] with
    | [] -> None
    | [op] -> Some (Po_kwd.kwd_of_string (YBU.to_string op))
    | lst -> raise (Malformed_json (`List lst |> YB.to_string))
                 
  (** Tests whether a list of guards includes a default node. *)
  let has_default (glist : ast_node list) =
    match List.hd (List.rev glist) with
    | Guard (POBoolean true) -> true
    | _ -> false

  let rec get_assignments ?(condition=(fun _ -> true))
                          (n : ast_node)
          : env_key list = match n with 
    | Skip _ | Return _ | Expr _ -> []
    | Seq node_list ->
      List.fold_left (fun lst n ->
          lst @ (get_assignments ~condition:condition n)) [] node_list
    | Cond conds ->
      List.fold_left (fun lst (guard, n) ->
          lst @ (get_assignments ~condition:condition n)) [] conds
    | Guard _ -> []
    | Assignment (o, label, i, e) ->
      if condition e
      then [(label, i)]
      else [] 

  (* Returns the phi nodes for deciding between versioned assignments. This 
  function gets called at the end of every cond parse. *)
  let make_phi_nodes im has_default (consequents: ast_node list) =
    (* Get all assignments for each cond. If there are any shared labels 
       between conds, make phi nodes. *)
    let conds_assigns : env_key list list = 
      List.map get_assignments consequents in 
    let labels = 
      Utils.uniq (List.flatten (List.map (List.map fst) conds_assigns)) in
    Logger.print_debug __LINE__ "Labels requiring phi nodes: [%s]" 
      (Utils.join "; " Utils.identity labels);
    (* if there is no default, then we assign the default to be the case where 
        all vars have an external value. *)
    (* let conds_assigns = conds_assigns @ (if has_default then [] else 
        [List.map (fun l -> (l, 0)) labels]) in *)
    let get_max_index label tuple_list =
      List.fold_left (fun max (s, i) ->
                      if s = label
                      then match max with
                          | None -> Some i
                          | Some i' -> if i' > i then Some i' else Some i
                      else max)
                    None
                    tuple_list 
    in
    Utils.filter_map 
      (fun label ->
          (* Not every label will need a phi node. *)
          let max_indices : int list = 
            Utils.filter_map (get_max_index label) conds_assigns in
          let new_indices = 
            max_indices @ 
            (if has_default && 
                List.length max_indices = List.length conds_assigns
             then []
             else [find_max_index label im]) in
          let phi = Phi (Unknown, label, new_indices) in
          let i = find_max_index label !global_max_index_map + 1 in
          global_max_index_map := IndexMap.add label i !global_max_index_map;
          Some (Assignment (Synth, label, i, phi)))
        labels


  let rec parse_json config im (ast : YB.json) : (ast_node * (int IndexMap.t)) =
    match get_op_kwd ast with
    | None -> Expr (make_literal config im ast), im
    | Some Po_kwd.Seq ->
      handle_seqs config im (YBU.member Po_kwd.seq ast) 
    | Some Po_kwd.Cond -> 
      handle_conds config im (YBU.member Po_kwd.cond ast)
    | Some Po_kwd.Set -> 
      handle_set config im (YBU.member Po_kwd.var ast) 
                           (YBU.member Po_kwd.value ast)
    | Some Po_kwd.Return -> 
      handle_return config im (YBU.member Po_kwd.value ast), im
    | _ -> Expr (handle_expr config im ast), im

  and make_literal ?(t=Unknown) config im e =
    match e with 
    | `Bool b -> Bexpr (POBoolean b)
    | `Float f ->
      (* May be written in scientific notation. *)
      Aexpr (PONumber (Oratio.ratio_of_float f e |> Oratio.reduce_ratio))
    | `Int i ->
      Aexpr (PONumber (Oratio.convert_to_reduced_ratio 
      (Oratio.I (Oratio.Integer i))))
    | `String s ->
      Sexpr (POString s)
    | `Null ->
      begin
        match t with
        | Unknown -> Null
        | Boolean -> Bexpr NullBoolean
        | Number -> Aexpr NullNumber
        | Container -> Cexpr NullContainer
        | String -> Sexpr NullString
      end
    | `List _ as ast -> Cexpr (handle_array config im ast)
    | ast ->            Cexpr (handle_map   config im ast)

  and handle_seqs config im = function
    | `List seqs ->
      let (seqs, im) = List.fold_left (fun (seqs, env) node ->
        let (s, e) = parse_json config env node in 
        (seqs @ [s], e))
        ([], im) seqs in 
      Seq seqs, im 
    | e -> raise (Malformed_json (e |> YB.to_string))      
  and handle_conds config im (js : YB.json) = match js with 
    | `List conds ->
      let prefixes = ref [] in
      (* Grab information about all of the variables defined before the guard. 
         This information can be used to find the latest bindings, globally, so
         far, and help with generating new indices. *)
      (* This information is only for locally visible bindings, to make sure we 
         grab the correct indices for the default (i.e., next-highest-up) 
         version of a variable. *)
      let conds' = List.map (fun cond ->
        let fi = YBU.member Po_kwd.fi cond in
        ignore (if (ast_contains_kv Po_kwd.op Po_kwd.weightedchoice fi 
                     || ast_contains_kv Po_kwd.op Po_kwd.uniformchoice fi)
                then 
                  raise (NYI "random var needs to be extracted from guard.")); 
        match get_op_kwd fi with
          | None -> (Guard (handle_bexpr config im fi),
                     parse_json config im (YBU.member Po_kwd.neht cond) |> fst)
          | Some Po_kwd.BernoulliTrial -> 
            let rv = handle_rv config im fi in
            let s = Po_format.string_of_expr (Sexpr (get_salt rv)) in 
            let o = Synth in 
            let m = Random in 
            let i = find_max_index s im in
            prefixes := Assignment (o, s, i, rv)::!prefixes;
            (Guard (GetBoolean (o, m, s, i)),  
            parse_json config im (YBU.member Po_kwd.neht cond) |> fst)
          | Some kwd' ->
            let guard = Guard (handle_bexpr config im fi) in
            let subsjs = (YBU.member Po_kwd.neht cond) in
            let subsequent = parse_json config im subsjs in
            (guard, subsequent |> fst))
            conds in
      let phi_nodes = make_phi_nodes im
        (has_default (List.map fst conds'))
        (List.map snd conds') in
      let im = List.fold_left (fun im node -> 
          match node with 
          | Assignment (o, s, i, _) -> 
            global_origin_map := OriginMap.add (s, i) o !global_origin_map;
            IndexMap.add s i im
          | _ -> im 
        ) im phi_nodes in 
      (* Update guards to have the appropriate type in the type environment *)
      if (List.length !prefixes) == 0
      then Seq ([Cond conds'] @ phi_nodes), im
      else Seq (List.rev !prefixes @ [Cond conds'] @ phi_nodes), im
    | js -> raise (Malformed_json (js|> YB.to_string))

  and handle_bexpr config im js =
    match get_op_kwd js with
    (* No keyword == boolean literal *)
    | None ->
      begin
        match make_literal ~t:Boolean config im js with
        | Aexpr e -> Not (BinNumOp (AEquals, e, PONumber Oratio.zero))
        | Bexpr b -> b
        | Cexpr e -> Not (BinCtrOp (CEquals, e, NullContainer))
        | Sexpr e -> Not (BinStrOp (SEquals, e, NullString))
        | e -> raise (GuardErr e)
      end
    | Some Po_kwd.Literal ->
      let t = Boolean in 
      begin
        match make_literal ~t config im (YBU.member Po_kwd.value js) with
        | Bexpr e -> e
        | Null -> NullBoolean
        | e -> raise (PlanOut_syntax (e, Boolean))
      end

    (* General get *)
    | Some Po_kwd.Get ->
      begin 
        match YBU.member Po_kwd.var js with
        | `String s -> make_get s im (fun o m s i -> GetBoolean (o, m, s, i))
        | js -> raise (Malformed_json (js|> YB.to_string))
      end
        
    (* Boolean expressions *)
    | Some Po_kwd.And ->
      begin 
        match YBU.member Po_kwd.values js with
        | `List (h1::h2::[]) ->
            BinBinOp (And, handle_bexpr config im h1, handle_bexpr config im h2)
        | `List (h1::h2::t) ->
            BinBinOp (And, handle_bexpr config im h1, 
                          handle_bexpr config im (`List (h2::t)))
        | l -> raise (Malformed_json (l|> YB.to_string))
      end
    | Some Po_kwd.Or -> 
      begin
        match YBU.member Po_kwd.values js with
        | `List (h1::h2::[]) -> 
            BinBinOp (Or, handle_bexpr config im h1, handle_bexpr config im h2)
        | `List (h1::h2::t) -> 
            BinBinOp (Or, handle_bexpr config im h1, 
                          handle_bexpr config im (`List (h2::t)))
        (* Some legacy form *)
        | `Assoc [("op", `String "array"); ("values", real_val_list)]
        | `Assoc [("values", real_val_list); ("op", `String "array")] ->
            let new_expr = 
              `Assoc [(Po_kwd.op, `String Po_kwd.or1); 
                      (Po_kwd.values, real_val_list)] in
            handle_bexpr config im new_expr
        | l -> raise (Malformed_json (l|> YB.to_string))
      end
    | Some Po_kwd.Not ->
      Not (handle_bexpr config im (YBU.member Po_kwd.value js))

    | Some Po_kwd.Equals ->
      begin
        let left = YBU.member Po_kwd.left js |> handle_expr config im in
        let right = YBU.member Po_kwd.right js |> handle_expr config im in
        match left, right with
        | Aexpr e1, Aexpr e2 -> BinNumOp (AEquals, e1, e2)
        | Sexpr e1, Sexpr e2 -> BinStrOp (SEquals, e1, e2)
        | Cexpr e1, Cexpr e2 -> BinCtrOp (CEquals, e1, e2)
        | Null, Aexpr e
        | Aexpr e, Null -> BinNumOp (AEquals, e, NullNumber)
        | Null, Sexpr e
        | Sexpr e, Null -> BinStrOp (SEquals, e, NullString)
        | Null, Cexpr e
        | Cexpr e, Null -> BinCtrOp (CEquals, e, NullContainer)
        | Get (o, m, s, i), Aexpr e
        | Aexpr e, Get (o, m, s, i) ->
            (* let i = find_max_index s im in
            let m = if i = 0 then External else Unclassified in  *)
            BinNumOp (AEquals, e, GetNumber (o, m, s, i))
        | e1, e2 -> Equals (e1, e2)
      end
    | Some Po_kwd.Lt
    | Some Po_kwd.Gt
    | Some Po_kwd.Lte
    | Some Po_kwd.Gte as kwd
      ->
      let left = handle_aexpr config im (YBU.member Po_kwd.left js) in
      let right = handle_aexpr config im (YBU.member Po_kwd.right js) in
      begin
        match kwd with
        | Some Po_kwd.Lt -> BinNumOp (Lt, left, right)
        | Some Po_kwd.Gt -> BinNumOp (Gt, left, right)
        | Some Po_kwd.Lte -> BinBinOp (Or,
            BinNumOp (AEquals, left, right),
            BinNumOp (Lt, left, right))
        | Some Po_kwd.Gte -> BinBinOp (Or,
            BinNumOp (AEquals, left, right),
            BinNumOp (Gt, left, right))
        | _ -> assert false
      end

    | Some Po_kwd.Index ->
      BIexpr (handle_cexpr config im (YBU.member Po_kwd.base js),
              handle_expr  config im (YBU.member Po_kwd.index js))
    | Some (Po_kwd.Custom name) ->
      let kvlist = handle_custom_values config im js in 
      let (rand_info, kvlist) = extract_rand_info name config kvlist im in 
      begin match POCfg.get_codomain name config with 
        | None 
        | Some Unknown 
        | Some Boolean ->
          CustomBoolean (name, kvlist, rand_info)
        | Some Number ->
          Not (BinNumOp (AEquals, PONumber Oratio.zero, 
                                  CustomNumber (name, kvlist, rand_info)))
        | Some Container ->
          (* Containers can be maps or arrays, so let's compare on length. *)
          Not (BinNumOp (AEquals, PONumber Oratio.zero,
                                  Length (CustomContainer (name, kvlist, 
                                  (match POCfg.get_codomain name config with
                                  | None -> Unknown
                                  | Some codomain -> codomain), rand_info))))
        | Some String ->
          Not (BinStrOp (SEquals, po_empty_string, 
            CustomString (name, kvlist, rand_info)))
      end 
    | Some (Po_kwd.Seq as k)
    | Some (Po_kwd.Cond as k)
    | Some (Po_kwd.Set as k)
    | Some (Po_kwd.Return as k) -> 
      raise (Malformed_json (
        Printf.sprintf 
          "Found a node keyword (%s) when expecting a boolean expression.
          \n\t%s\n"
          (Po_kwd.string_of_kwd k)
        (YB.to_string js)))
    | Some Po_kwd.BernoulliTrial ->
      begin match handle_rv config im js with 
        | RandomVar (weights, choices, unit, salt) ->
          RandomBoolean (weights, choices, unit, salt)
        | _ -> assert false 
      end 
    | Some k -> Printf.printf "Unexpected keyword in boolean: %s\n" 
      (Po_kwd.string_of_kwd k); assert false


  and handle_aexpr config im js =
    match get_op_kwd js with
    (* Numeric literal *)
    | None ->
      begin
        match make_literal ~t:Number config im js with
        | Aexpr a -> a
        | Null -> NullNumber
        | e -> raise (PlanOut_syntax (e, Number))
      end
    | Some Po_kwd.Literal ->
      begin 
        match make_literal ~t:Number config im (YBU.member Po_kwd.value js) with
        | Aexpr e -> e
        | Null -> NullNumber
        | e -> raise (PlanOut_syntax (e, Number))
      end
        
    (* A reference we know to have a numeric type *)
    | Some Po_kwd.Get ->
      begin
        match YBU.member Po_kwd.var js with
        | `String s -> make_get s im (fun o m s i -> GetNumber (o, m, s, i))
        | js -> raise (Malformed_json (js|> YB.to_string))
      end

    (* Operations on containers. *)
    | Some Po_kwd.Length ->
      Length (YBU.member Po_kwd.value js |> handle_cexpr config im)


    (* Arithmetic expressions *)
    | Some Po_kwd.Sum ->
      begin
        match YBU.member Po_kwd.values js with
        | `List (h1::h2::[]) -> 
            Abinop (Sum, handle_aexpr config im h1, 
                         handle_aexpr config im h2)
        | `List (h1::h2::t) ->
            let new_expr = 
              `Assoc [(Po_kwd.op, `String Po_kwd.sum); (Po_kwd.values, `List (h2::t))] in
            Abinop (Sum, handle_aexpr config im h1, 
                         handle_aexpr config im new_expr)
        (* Legacy crap *)
        | `Assoc [("op", `String "array"); ("values", real_arg_list)]
        | `Assoc [("values", real_arg_list); ("op", `String "array")] ->
            let new_expr = 
              `Assoc [(Po_kwd.op, `String Po_kwd.sum); (Po_kwd.values, real_arg_list)] in
            handle_aexpr config im new_expr
        | l -> raise (Malformed_json (l|> YB.to_string))
      end
    | Some Po_kwd.Negative ->
      Abinop (Product, PONumber Oratio.neg_one, 
        handle_aexpr config im (YBU.member Po_kwd.value js))
    | Some Po_kwd.Product ->
      begin
        match YBU.member Po_kwd.values js with
        (* This case is due to some weird legacy AST stuff where values is an 
        object and not a list, and that object is an array. *)
        | `Assoc [("op", `String "array"); ("values", real_arg_list)]
        | `Assoc [("values", real_arg_list); ("op", `String "array")] ->
            let new_expr = 
              `Assoc [(Po_kwd.op, `String Po_kwd.product); 
                      (Po_kwd.values, real_arg_list)] in
            handle_aexpr config im new_expr 
        | `List (h1::h2::[]) ->
            Abinop (Product, handle_aexpr config im h1, 
                             handle_aexpr config im h2)
        | `List (h1::h2::t) ->
            Abinop (Product,
                    handle_aexpr config im h1,
                    handle_aexpr config im 
                      (`Assoc [(Po_kwd.op, `String Po_kwd.product);
                    (Po_kwd.values, `List (h2::t))]))
        | l -> raise (Malformed_json (l|> YB.to_string))
      end
    | Some Po_kwd.Index ->
      begin
        let base  = handle_expr config im (YBU.member Po_kwd.base js) in
        let index = handle_expr config im (YBU.member Po_kwd.index js) in
        (*let msg = "Base of indexable must have type cexpr; is: " in*)
        match base with
        | Null 
        | Aexpr _ 
        | Bexpr _ 
        | Sexpr _ 
            -> raise (PlanOut_syntax (base, Container))
        | Cexpr c -> AIexpr (c, index)
        | Get (o, _, s, _) ->
          let i = find_max_index s im in
          let m = if i = 0 then External else Unclassified in 
          AIexpr (GetContainer (o, m, s, i, Number), index)
        | CustomExpr (name, kvlist, salt) -> 
          AIexpr (CustomContainer (name, kvlist, Unknown, None), index)
        | Coalesce (attempt, default) -> raise (NYI empty_string)
        | Iexpr (base', index') -> AIexpr(CIexpr(base', index'), index) 
        | RandomVar _ -> raise (NYI empty_string)
        | Phi _ -> assert false
      end
    | Some Po_kwd.Mod | Some Po_kwd.Div as kwd ->
      let get_constructor kwd left right =
        match kwd with
        | Some Po_kwd.Mod -> Abinop (Mod, left, right)
        | Some Po_kwd.Div -> Abinop (Div, left, right)
        | _ -> assert false
      in
      let left  = handle_aexpr config im (YBU.member Po_kwd.left js) in
      let right = handle_aexpr config im (YBU.member Po_kwd.right js) in
      get_constructor kwd left right
    | Some (Po_kwd.Custom name) ->
      let kvlist = handle_custom_values config im js in 
      let (rand_info, kvlist) = extract_rand_info name config kvlist im in 
      begin match POCfg.get_codomain name config with 
        | None 
        | Some Unknown
        | Some Number -> 
          CustomNumber (name, kvlist, rand_info)
        | Some codomain -> 
          raise (make_coersion_err name ~t_from:codomain ~t_to:Number) 
      end 
    | Some Po_kwd.Coalesce ->
      let (c : po_expr) = 
        handle_coalesce config im (YBU.member Po_kwd.values js) in
      begin
        match c with
        | Coalesce (attempt, Aexpr default) -> 
          CoalesceNumber (to_number attempt, default)
        | _ -> 
          Printf.printf "Numeric Coalesce error: %s\n\t%s\n\t%s"
            (Po_format.string_of_expr c)
            (Po_format.ast_string_of_expr c)
            (YB.to_string js);
          assert false
      end

    | Some Po_kwd.WeightedChoice -> 
      let rv = handle_rv config im js in 
      to_number rv

    | Some kwd ->
      raise (CodomainMismatch (kwd, Number, js))

  and handle_sexpr config im js : po_sexpr =
    match get_op_kwd js with
    (* String literal *)
    | None ->
      begin
        match make_literal ~t:String config im js with
        | Sexpr s -> s
        | Null -> NullString
        | e -> raise (PlanOut_syntax (e, String))
      end
      
    | Some Po_kwd.Literal ->
      begin
        match make_literal config im (YBU.member Po_kwd.value js) with
        | Sexpr s -> s
        | e -> raise (PlanOut_syntax (e, String))
      end 

    (* A reference whose type we know to be a string. *)
    | Some Po_kwd.Get ->
      begin
        match YBU.member Po_kwd.var js with
        | `String s -> make_get s im (fun o m s i -> GetString (o, m, s, i))
        | js -> raise (Malformed_json (js|> YB.to_string))
      end
    | Some Po_kwd.Index ->
      begin
        let base  = handle_expr config im (YBU.member Po_kwd.base js) in
        let index = handle_expr config im (YBU.member Po_kwd.index js) in
        match base with
        | Cexpr c -> SIexpr (c, index)
        | Get (o, m, s, i) -> SIexpr (GetContainer (o, m, s, i, String), index)
        | e -> raise (PlanOut_syntax (e, Container))
      end
    | Some (Po_kwd.Custom name) ->
      let kvlist = handle_custom_values config im js in 
      let (rand_info, kvlist) = extract_rand_info name config kvlist im in 
      begin match POCfg.get_codomain name config with 
        | None 
        | Some Unknown 
        | Some String -> CustomString (name, kvlist, rand_info)
        | Some codomain -> 
          raise (make_coersion_err name ~t_from:codomain ~t_to:String)
      end
    | Some k -> assert false

  and handle_expr config (im : int IndexMap.t) js : po_expr =
    match get_op_kwd js with
      | None -> make_literal config im js
      | Some Po_kwd.BernoulliTrial
      | Some Po_kwd.BernoulliFilter
      | Some Po_kwd.RandomInteger
      | Some Po_kwd.UniformChoice
      | Some Po_kwd.WeightedChoice
      | Some Po_kwd.Sample
        -> handle_rv config im js
      | Some Po_kwd.Get -> handle_get im (YBU.member Po_kwd.var js)
      (* cexpr types *)
      | Some Po_kwd.Array | Some Po_kwd.Map ->
        Cexpr (handle_cexpr config im js)
      | Some Po_kwd.Literal ->
        let v = YBU.member Po_kwd.value js in
        begin match v with
          | `Null ->     make_literal            config im v
          | `String _ -> make_literal ~t:String  config im v
          | `Float _  -> make_literal ~t:Number  config im v
          | `Int _ ->    make_literal ~t:Number  config im v
          | `Bool _ ->   make_literal ~t:Boolean config im v
          | _ ->         handle_json config im v
        end
        (* aexpr types *)
      | Some Po_kwd.Product
      | Some Po_kwd.Sum
      | Some Po_kwd.Negative
      | Some Po_kwd.Mod
      | Some Po_kwd.Div
      | Some Po_kwd.Length
        -> Aexpr (handle_aexpr config im js)
      (* bexpr types *)
      | Some Po_kwd.Gt
      | Some Po_kwd.Gte 
      | Some Po_kwd.Lt
      | Some Po_kwd.Lte
      | Some Po_kwd.Not
      | Some Po_kwd.And
      | Some Po_kwd.Equals
      | Some Po_kwd.Or
        -> Bexpr (handle_bexpr config im js)
      | Some Po_kwd.Index ->
          Iexpr (handle_cexpr config im (YBU.member Po_kwd.base js),
                handle_expr config im (YBU.member Po_kwd.index js))
      | Some Po_kwd.Coalesce -> 
        handle_coalesce config im (YBU.member Po_kwd.values js)
      | Some (Po_kwd.Custom name) ->
        let kvlist     = handle_custom_values config im js in 
        let (rand_info, kvlist) = extract_rand_info name config kvlist im in 
        begin match POConfig.get_codomain name config with
          | None 
          | Some Unknown -> CustomExpr (name, kvlist, rand_info)
          | Some Number -> Aexpr (CustomNumber (name, kvlist, rand_info))
          | Some Boolean -> Bexpr (CustomBoolean (name, kvlist, rand_info))
          | Some Container -> Cexpr (CustomContainer (name, kvlist, Unknown, rand_info))
          | Some String -> Sexpr (CustomString (name, kvlist, rand_info))
        end
      | Some (Po_kwd.Seq as k)
      | Some (Po_kwd.Cond as k)
      | Some (Po_kwd.Set as k)
      | Some (Po_kwd.Return as k) -> 
        raise (Malformed_json (
          Printf.sprintf 
            "Found a node keyword (%s) when expecting an expression.\n\t%s\n"
            (Po_kwd.string_of_kwd k)
          (YB.to_string js)))
      | Some op -> Printf.printf "Found op %s where it shouldn't be\n" 
        (Po_kwd.string_of_kwd op); assert false

  and handle_custom_values config im js : (string * po_expr) list =
    match js with
    | `Assoc kvlist ->
      List.filter (fun (k, _) -> compare k Po_kwd.op <> 0) kvlist
      |> List.map (fun (k, v) -> (k, handle_expr config im v)) 
    | js -> raise (Malformed_json (js|> YB.to_string))

  and handle_cexpr config im js : po_cexpr =
    match get_op_kwd js with
    | None -> raise (Malformed_json (js|> YB.to_string))
    | Some Po_kwd.Array ->
      handle_array config im (YBU.member Po_kwd.values js)
    | Some Po_kwd.Map ->
      handle_map config im js
    | Some Po_kwd.Index ->
      begin
        (* This is the base of some other indexing operation. This base is 
          itself the result of an indexing operation. *)
        let e = handle_expr config im js in
        match e with
        | Iexpr ((base : po_cexpr), (index : po_expr)) ->
            CIexpr (base, index)
        | _ -> raise (PlanOut_syntax (e, Unknown))
      end
    | Some Po_kwd.Get ->
      begin
        match YBU.member Po_kwd.var js with
        | `String s -> 
          make_get s im (fun o m s i -> GetContainer (o, m, s, i, Unknown))
        | js' -> raise (Malformed_json (js'|> YB.to_string))
      end
    | Some (Po_kwd.Custom name) ->
      let kvlist     = handle_custom_values config im js in 
      let (rand_info, kvlist) = extract_rand_info name config kvlist im in 
      CustomContainer (name, kvlist, Unknown, rand_info)
    | Some k -> assert false

  and handle_coalesce config im = function
    | `List [attempt ; default] ->
      Coalesce (handle_expr config im attempt, handle_expr config im default)
    | js -> raise (Malformed_json (js|> YB.to_string))

  and handle_set config im lhs rhs : (ast_node * int IndexMap.t) =
    let o = Source in 
    let label : string    = YBU.to_string lhs in
    let i                 = find_max_index label !global_max_index_map + 1 in
    let node : po_expr    = handle_expr config im rhs in
    global_max_index_map := IndexMap.add label i !global_max_index_map;
    global_origin_map    := OriginMap.add (label, i) o !global_origin_map;
    (* _env := Po_env.add ~o (label, i) node !_env; *)
    (* let env = Po_env.add (label, i) node env in  *)
    let salt_from current_salt = 
      if current_salt = po_empty_string || current_salt = NullString then
        POString label
      else
        current_salt
        in
    let transformed_random = match node with 
      | RandomVar (weights, choices, unit, current_salt) ->
        RandomVar (weights, choices, unit, salt_from current_salt)
      | _ -> node in 
    (Assignment (o, label, i, transformed_random), IndexMap.add label i im)

  and handle_return config im arg =
    let retarg = handle_bexpr config im arg in 
    Return retarg

  and handle_map config (im : int IndexMap.t) = function
    (* | `Null -> NullContainer *)
    | js -> (* grab all the keys and values that aren't maps *)
      POMap (Unknown,
        List.fold_left (fun m (k, v) -> if compare k Po_kwd.op <> 0
                then POMap_.add k (handle_expr config im v) m
                else m)
          POMap_.empty
          (YBU.to_assoc js))

  and handle_json config im js : po_expr =
    (* Cexpr (POJson js) *)
    match js with
    | `List _ ->  Cexpr (handle_array config im js)
    | `Assoc _ -> Cexpr (handle_map   config im js)
    | _ ->        make_literal config im js

  and handle_array config im : YB.json -> po_cexpr = function
    | `List values ->
      let arr =  List.map (handle_expr config im) values in
      POArray (Unknown, arr)
    | js -> raise (Malformed_json (js|> YB.to_string))
          
  and handle_get im = function
    | `String "null" -> Null
    | `String s -> make_get s im (fun o m s i -> Get (o, m, s, i))
    | js -> raise (Malformed_json (js|> YB.to_string))

  and handle_uexpr config (im : int IndexMap.t) js =
    let handle_uexpr = handle_uexpr config im in 
    let to_unit = to_unit config im in 
    match YBU.filter_member Po_kwd.op [js] with
    | [op] -> 
      begin match Po_kwd.kwd_of_string (YBU.to_string op) with
      | Po_kwd.Get ->
        begin match YBU.member Po_kwd.var js with
        | `String "userid" -> Userid
        | `String s -> 
          begin match split_id s with
          | [stem; "id"] -> Id stem
          | [u] -> UnitR u
          | u -> 
            raise (InvalidUnitIdentifier (Utils.join ", " Utils.identity u))
          end
        | e -> raise (NYI ("handle_uexpr: " ^ YB.to_string e))
        end
      | Po_kwd.Array ->
        begin match YBU.member Po_kwd.values js with
        | `List [u1] -> handle_uexpr u1
        | `List [u1; u2] -> Tuple2 (handle_uexpr u1, handle_uexpr u2)
        | `List [u1; u2; u3] -> Tuple3 (handle_uexpr u1, handle_uexpr u2, 
          handle_uexpr u3)
        | `List [u1; u2; u3; u4] -> Tuple4 (handle_uexpr u1, handle_uexpr u2, 
          handle_uexpr u3, handle_uexpr u4)
        | js -> raise (Malformed_json (js|> YB.to_string))
        end
      | k -> handle_expr config im js |> to_unit
      end
    | _ -> raise (Malformed_json (js |> YB.to_string))

  and to_unit config (im : int IndexMap.t) (e : po_expr) : po_uexpr =
    let custom_ctor _ _ _ = raise (Malformed_unit e) in 
    let get_ctor o m s i = 
      (*if o = ExtSource && m = External && i = 0
      then `Assoc [(Po_kwd.op, `String Po_kwd.get); (Po_kwd.var, `String s)] 
            |> handle_uexpr
      else raise (Malformed_unit e) in *)
      `Assoc [(Po_kwd.op, `String Po_kwd.get); (Po_kwd.var, `String s)] 
            |> handle_uexpr config im in 
    let coalesce_ctor attempt default = raise (Malformed_unit e) in 
    let iexpr_ctor base inde = raise (Malformed_unit e) in 
    let rand_ctor weights choices unit salt = raise (Malformed_unit e) in 
    let cfn e = match e with 
      | POArray (_, arr) -> 
        let get_s_from_get e' = match e' with 
          | Get (_, _, s, _) -> s
          | _ -> raise (Malformed_unit (Cexpr e)) in 
        let gets = List.map get_s_from_get arr 
          |> List.map (fun s -> `Assoc [(Po_kwd.op, `String Po_kwd.get);
                                        (Po_kwd.var, `String s)]) in 
        handle_uexpr config im (`Assoc [(Po_kwd.op, `String Po_kwd.array);
                                        (Po_kwd.values, `List gets)])
      | _ -> raise (Malformed_unit (Cexpr e)) in 
    Po_syntax.to_type (Id "NULL")
      (* ~afn:(fun e -> raise (Malformed_unit (Aexpr e))) *)
      ~afn:(fun e -> UExpr (Aexpr e))
      ~bfn:(fun e -> raise (DataFlowDeterminism (Bexpr e)))
      (* this will prevent us from having multiple units for external functions. *)
      (* ~cfn:(fun e -> raise (Malformed_unit (Cexpr e))) *)
      ~cfn
      ~sfn:(fun e -> UExpr (Sexpr e))
      ~custom_ctor
      ~get_ctor
      ~coalesce_ctor
      ~iexpr_ctor
      ~rand_ctor 
      e
  and extract_rand_info name config kvlist im = 
    (*Printf.printf "config: %s\n" (POCfg.string_of_typequals config);*)
    let maybe_unit = POCfg.get_unit name config in      
    
    let rand_info = begin if POCfg.is_random name config 
      then 
        let unit_arg = Utils.extract maybe_unit in
        let unit_value = (try
              List.assoc unit_arg kvlist |> to_unit config im 
            with Not_found -> 
              raise (UnitError (Printf.sprintf "Unknown unit: %s" unit_arg)))
          in 
        let salt = if List.mem_assoc "salt" kvlist 
          then List.assoc "salt" kvlist |> to_string 
          else po_empty_string in 
        Some {unit_arg; unit_value; salt}
      else None end in 
    let kvlist = match rand_info with 
    | None -> kvlist 
    | Some _ -> List.remove_assoc (Utils.extract maybe_unit) kvlist in 
    (rand_info, kvlist)    

  and handle_rv_choices config im ast rv_type =
    match Po_kwd.kwd_of_string rv_type with
    | Po_kwd.BernoulliTrial ->
      POArray (Boolean, [Bexpr (POBoolean false); Bexpr (POBoolean true) ])
    | Po_kwd.BernoulliFilter ->
      raise (NYI "I don't know what bernoulliFilter does, but it's a valid 
      built-in operator.")
    | Po_kwd.UniformChoice | Po_kwd.WeightedChoice ->
      begin 
        match handle_expr config im (YBU.member Po_kwd.choices ast) with
        | Cexpr e -> e
        | Get (o, m, s, i) -> GetContainer (o, m, s, i, Unknown)
        | Iexpr (base, index) -> CIexpr (base, index)
        | CustomExpr (name, kvlist, salt) -> CustomContainer (name, kvlist, Unknown, salt)
        | e -> raise (PlanOut_syntax (e, Unknown))
      end
    | Po_kwd.RandomInteger ->
      (* Add a range operator *)
      let min = handle_aexpr config im (YBU.member Po_kwd.min ast) in
      let max = handle_aexpr config im (YBU.member Po_kwd.max ast) in
      Range (min, max)
    | Po_kwd.Sample ->
      let choices = handle_cexpr config im (YBU.member Po_kwd.choices ast) in
      let num_draws = (match YBU.member Po_kwd.num_draws ast with
            | `Null -> Length choices
            | n -> handle_aexpr config im n) in
      EnumChoose (choices, num_draws)
    | _ -> assert false

  and promote_to_aiexpr base index =
    match base with
    | CIexpr (base', index') -> AIexpr (CIexpr (base', index'), index')
    | _ -> assert false

  and handle_rv_weights config im ast rv_type choices =
    match Po_kwd.kwd_of_string rv_type with
    | Po_kwd.BernoulliTrial ->
      let open Oratio in 
      begin match handle_expr config im (YBU.member Po_kwd.p ast) with
        | Aexpr (PONumber p) ->
          let prob_success = Aexpr (PONumber p) in 
          let prob_failure = Aexpr (PONumber (subtract one p)) in 
          POArray (Number, [prob_failure; prob_success])
        | Aexpr e ->
          let prob_success = Aexpr e in 
          let prob_failure = Aexpr (Abinop (Sum, PONumber one,
                                    Abinop (Product, PONumber neg_one, e))) in 
          POArray (Number, [prob_failure; prob_success])
        | Bexpr (POBoolean true) ->
          POArray (Number, [Aexpr (PONumber zero); Aexpr (PONumber one)])
        | Bexpr (POBoolean false) ->
          POArray (Number, [Aexpr (PONumber one); Aexpr (PONumber zero)])
        | Get (o, _, s, _) ->
            let i = find_max_index s im in
            let negative_s = Abinop (Product, 
              PONumber neg_one, 
              GetNumber (o, Unclassified, s, i)) in
            POArray (Number, [Aexpr (Abinop (Sum, PONumber one, negative_s));
                              Aexpr (GetNumber (o, Unclassified, s, i))])
        | Iexpr (base, index) ->
            let p = AIexpr (base, index) in
            POArray (Number, [Aexpr (Abinop (Sum,
              PONumber one,
              Abinop (Product, PONumber neg_one, p)));
            Aexpr p])
        | e -> raise (PlanOut_syntax (e, Po_env.get_expression_type e))
      end
    | Po_kwd.UniformChoice ->
      let open Oratio in 
      begin match choices with
        | POArray (_, arr) ->
          let num_choices = List.length arr in
          let make_uniform_weights _ =
            Aexpr (PONumber (ratio_of_num_et_den 1 num_choices)) in
          let weight_arr = List.map make_uniform_weights arr in
          POArray (Number, weight_arr)
        | GetContainer _ as get ->  
          Repeat (Length get, Aexpr (Abinop (Div, PONumber one, Length get)))
        | EnumChoose _ -> raise (NYI "sample")
        | CustomContainer _ as e -> e
        | e -> raise (PlanOut_syntax (Cexpr e, Container))
      end
    | Po_kwd.Sample ->
      begin
        let stuff = (match ast with `Assoc a -> a | _ -> assert false) in
        match handle_expr config im (YBU.member Po_kwd.weights ast) with
          | Null ->
            let new_ast = `Assoc (Utils.replace stuff
                  (Utils.index_of stuff (Po_kwd.op, `String Po_kwd.sample))
                  (Po_kwd.op, `String Po_kwd.uniformchoice)) in
            handle_rv_weights config im new_ast Po_kwd.uniformchoice choices 
        | _ ->
            let new_ast = `Assoc (Utils.replace stuff
                  (Utils.index_of stuff (Po_kwd.op, `String Po_kwd.sample))
                  (Po_kwd.op, `String Po_kwd.weightedchoice)) in
            handle_rv_weights config im new_ast Po_kwd.weightedchoice choices
      end 
    | Po_kwd.WeightedChoice ->
      begin match handle_expr config im (YBU.member Po_kwd.weights ast) with
        | Cexpr e -> e
        | Get (o, m, s, i) -> GetContainer (o, m, s, i, Unknown)
        | Iexpr (base, index) -> CIexpr (base, index)
        | e -> raise (PlanOut_syntax (e, Container))
      end
    | Po_kwd.RandomInteger ->
      (* Since we normalize weights anyway, we can just do a range on the sum. *)
      let min = handle_aexpr config im (YBU.member Po_kwd.min ast) in
      let max = handle_aexpr config im (YBU.member Po_kwd.max ast) in
      (* ranges are index-inclusive, so size is 
        max - min + 1
        1 + max + (-min)
        1 + (max + (min * -1))
      *)
      (* When we use a range in the weights for the rangom integer, we need to 
      remember that these are expanded into constants of 1, not indices, nor 
      values to select. *)
      let num_choices = Length (Range (min, max)) in
      Repeat (num_choices, Aexpr (Abinop (Div, PONumber Oratio.one, num_choices)))
    | kwd -> assert false
      
  and handle_rv config im (ast: YB.json) =
    let rv_type = YBU.member Po_kwd.op ast |> YBU.to_string in

    let choices : po_cexpr = handle_rv_choices config im ast rv_type in 
    let weights : po_cexpr = handle_rv_weights config im ast rv_type choices in
    let unit : po_uexpr = 
      if YBU.member Po_kwd.unit ast <> `Null
      then handle_uexpr config im (YBU.member Po_kwd.unit ast) 
      else raise (MissingUnitError (Po_kwd.unit, 
        YBU.keys ast |> List.filter ((<>) Po_kwd.op))) in 
    let salt : po_sexpr = YBU.member Po_kwd.salt ast 
      |> handle_sexpr config im in 
    (* If the weights and/or choices are json arrays, convert them to  
    arrays *)
    RandomVar (poarr_of_jsonarr weights, 
               poarr_of_jsonarr choices, unit, salt)

  and poarr_of_jsonarr = function
    | POArray _
    | GetContainer _
    | Range _
    | Repeat _ 
    | CIexpr _
    | EnumChoose _
    | CustomContainer _
      as e -> e
    | e -> raise (PlanOut_syntax (Cexpr e, Container))
  
  let make_program config js : program =
    global_max_index_map := IndexMap.empty;
    let incomplete = Malformed_json (js |> YB.to_string) in
    match js with
    | `Assoc _ -> begin
      let op = js |> YBU.member "op" in
      match (op, js) with
      | (`String "seq", `Assoc alist) ->
          let in_experiment = "in_experiment" in 
          let (seq, _) = parse_json config IndexMap.empty js in
          let p = Program seq in 
          (* This was the old way of turning logging on and off. *)
          if Po_aux.is_var_in_program p in_experiment 
          then begin match seq with
          | Seq seqs ->
            begin match List.rev seqs with 
              (* If it already has a return, don't append. *)
              | (Return _)::t -> Program seq
              | _ -> 
                let o = Source in 
                let i = find_max_index in_experiment !global_max_index_map in 
                let return = Return (GetBoolean (o, Unclassified, 
                  in_experiment, i)) in 
                Program (Seq (seqs @ [return]))
            end
          | _ -> assert false end 
          else Program seq
      | _ -> raise incomplete
          end
      | _ -> raise incomplete

end
