(** Dependencies:
    - Po_env 
    - Po_syntax 
  *)

(* conisider making a functor that takes a function that 
  extracts the varidset type from gets *)
open Sexplib.Conv
open Po_syntax

type env = Po_env.env 


module Types = Map.Make(String)
module Params = Config.Params
type varidset = Params.t 
let sexp_of_varidset v = [%sexp_of: Config.ssa_id list] (Params.elements v)
let varidset_of_sexp (s : Sexplib.Sexp.t) : varidset = match s with 
| Sexplib.Sexp.List sexps -> 
  List.fold_right Params.add (List.map Config.ssa_id_of_sexp sexps) Params.empty
| _ -> assert false

let rec flatten_seqs = function
  | [] -> []
  | (Seq seqs)::t -> (flatten_seqs seqs) @ (flatten_seqs t)
  | h::t -> h::(flatten_seqs t)
  
let get_node_vars ?(astfn=fun _ -> true) 
                  ?(efn=fun _ -> true) 
                  ?(afn=fun _ -> true)
                  ?(bfn=fun _ -> true)
                  ?(cfn=fun _ -> true)
                  ?(sfn=fun _ -> true) 
                  p =
let rec custom_params kvlist pset = 
  kvlist 
  |> List.filter (fun (_, v) -> efn v)
  |> List.map (fun (_, v) -> gv_exp pset v) 
  |> List.fold_left Params.union pset
and gv_node pset n = match n with 
  | Skip _ -> pset 
  | Assignment (_, s, i, e) -> 
    gv_exp (if astfn n then Params.add (s, i) pset else pset) e 
  | Guard b 
  | Return b -> gv_bexp pset b
  | Expr e -> gv_exp pset e 
  | Seq seqs -> List.fold_left gv_node pset seqs
  | Cond conds ->
    let fn pset (g, n) = gv_node (gv_node pset g) n in 
    List.fold_left fn pset conds
and gv_exp pset n = match n with  
  | Phi (_, name, indices) -> 
    if efn n 
    then List.fold_left (fun p i -> Params.add (name, i) p) pset indices
    else pset 
  | Null -> pset
  | CustomExpr (_, kvlist, _) -> 
      custom_params kvlist pset
  | Aexpr e -> gv_aexp pset e 
  | Bexpr e -> gv_bexp pset e 
  | Cexpr e -> gv_cexp pset e 
  | Sexpr e -> gv_sexp pset e 
  | Get (_, _, s, i) -> 
    if efn n then Params.add (s, i) pset else pset 
  | Coalesce (attempt, default) ->
    Params.union (gv_exp pset attempt) (gv_exp pset default)
  | Iexpr (base, index) ->
    Params.union (gv_cexp pset base) (gv_exp pset index)
  | RandomVar (weights, choices, _, _) ->
    Params.union (gv_cexp pset weights) (gv_cexp pset choices)
and gv_cexp pset e = match e with  
  | CustomContainer (_, kvlist, _, _) -> custom_params kvlist pset
  | RandomContainer (weights, choices, _, _) ->
    Params.union (gv_cexp pset weights) (gv_cexp pset choices)
  | NullContainer -> pset 
  | CoalesceContainer (attempt, default) ->
    Params.union (gv_cexp pset attempt) (gv_cexp pset default)   
  | POArray (_, elist) -> List.fold_left gv_exp pset elist 
  | POMap (_, m) -> 
    List.fold_left gv_exp pset (POMap_.bindings m |> List.map snd)
  | GetContainer (_, _, s, i, _) -> 
    if cfn e then Params.add (s, i) pset else pset 
  | CIexpr (base, index) ->
    Params.union (gv_cexp pset base) (gv_exp pset index)
  | Range (low, high) ->
    Params.union (gv_aexp pset low) (gv_aexp pset high)
  | Repeat (times, item) ->
    Params.union (gv_exp pset item) (gv_aexp pset times)           
  | EnumChoose (sample, size) ->
    Params.union (gv_cexp pset sample) (gv_aexp pset size)
and gv_sexp pset e = match e with 
  | CustomString (_, kvlist, _) -> custom_params kvlist pset
  | RandomString (weights, choices, _, _) ->
    Params.union (gv_cexp pset weights) (gv_cexp pset choices)
  | CoalesceString _
  | POString _
  | NullString -> pset
  | GetString (_, _, s, i) -> 
    if sfn e then Params.add (s, i) pset else pset 
  | SIexpr (base, index) ->
    Params.union (gv_cexp pset base) (gv_exp pset index)
and gv_aexp pset e = match e with 
  | NullNumber 
  | PONumber _ -> pset 
  | CustomNumber (_, kvlist, _)  -> custom_params kvlist pset
  | RandomNumber (weights, choices, _, _) ->
    Params.union (gv_cexp pset weights) (gv_cexp pset choices)
  | GetNumber (_, _, s, i) -> 
    if afn e then Params.add (s, i) pset else pset 
  | CoalesceNumber (attempt, default) ->
    Params.union (gv_aexp pset attempt) (gv_aexp pset default)
  | AIexpr (base, index) ->
    Params.union (gv_cexp pset base) (gv_exp pset index)
  | Length e ->
    gv_cexp pset e
  | Abinop (_, e1, e2) ->
    Params.union (gv_aexp pset e1) (gv_aexp pset e2)
and gv_bexp pset e = match e with 
  | NullBoolean
  | POBoolean _ -> pset
  | CustomBoolean (_, kvlist, _) -> custom_params kvlist pset
  | RandomBoolean (weights, choices, _, _) ->
    Params.union (gv_cexp pset weights) (gv_cexp pset choices)
  | GetBoolean (_, _, s, i) -> 
    if bfn e then Params.add (s, i) pset else pset 
  | CoalesceBoolean (attempt, default) 
    -> Params.union (gv_bexp pset attempt) (gv_bexp pset default)
  | BIexpr (base, index) 
    -> Params.union (gv_cexp pset base) (gv_exp pset index)
  | Not e -> gv_bexp pset e
  | BinBinOp (And, e1, e2)
  | BinBinOp (Or, e1, e2) 
    -> Params.union (gv_bexp pset e1) (gv_bexp pset e2)
  | Equals (lhs, rhs)
    -> Params.union (gv_exp pset lhs) (gv_exp pset rhs)
  | BinBinOp (_, e1, e2)
    -> Params.union (gv_bexp pset e1) (gv_bexp pset e2) 
  | BinStrOp (_, e1, e2) 
    -> Params.union (gv_sexp pset e1) (gv_sexp pset e2)
  | BinCtrOp (_, e1, e2) 
    -> Params.union (gv_cexp pset e1) (gv_cexp pset e2)
  | BinNumOp (_, e1, e2) 
    -> Params.union (gv_aexp pset e1) (gv_aexp pset e2)
in gv_node Params.empty p

let get_program_vars (Program p) = 
get_node_vars p

let get_guard_vars (Program p) = 
let select_fn = function 
| Guard _ | Cond _ | Seq _ -> true
| _ -> false in 
get_node_vars ~astfn:select_fn p

let get_path_vars nodes =
List.map get_node_vars nodes
|> List.fold_left Params.union Params.empty

let rec get_all_assignments node : varidset = 
let astfn = function Assignment _ -> true | _ -> false in
let efn _ = false in 
get_node_vars ~astfn ~efn node
        
let is_var_in_program p name =
get_program_vars p 
|> Params.filter (fun (s, i) -> s = name)
|> Params.cardinal
|> (<) 0

let expr_external = function 
| CustomExpr (name, _, _)
| Aexpr (CustomNumber (name, _, _))
| Bexpr (CustomBoolean (name, _, _))
| Cexpr (CustomContainer (name, _, _, _))
| Sexpr (CustomString (name, _, _)) -> Some name 
| _ -> None

let get_expression_type = function
| Aexpr _ -> Number
| Bexpr _ -> Boolean
| Cexpr _ -> Container
| Sexpr _ -> String
| _ -> Unknown

let get_phi_type env s ints = 
let types = List.map (fun i -> 
    if Po_env.mem (s, i) env 
    then Po_env.find (s, i) env |> get_expression_type
    else Unknown) ints
  |> List.filter (fun t -> t <> Unknown) in 
let conflict_list = List.filter (fun t -> t <> Boolean) types
                    |> Utils.uniq in 
if List.length types = 0
then Unknown
else match conflict_list with 
  | [] -> Boolean
  | [t] -> t
  | t1::t2::_ -> 
    raise (type_error ~expected:t1 ~found:t2 (Phi (Unknown, s, ints)))


let is_bernoulli_trial ~choices : bool = 
let open Oratio in 
match choices with
| POArray (_, [Bexpr (POBoolean false); Bexpr (POBoolean true)])
| POArray (_, [Bexpr (POBoolean true); Bexpr (POBoolean false)])
  -> true
(*| POArray (_, [Aexpr (PONumber n1); Aexpr (PONumber n2)])
  -> (n1 = zero &&  n2 = one) || (n2 = zero && n1 = one) *)
| _ -> false

let is_uniform_choice ~weights : bool = match weights with 
| POArray (t, _) when t <> Number && t <> Unknown -> 
  type_error ~expected:Number ~found:t (Cexpr weights)
| POArray (_, []) -> true
| POArray (_, Aexpr (PONumber h)::t)
    when (List.for_all (fun n -> match n with
          | Aexpr (PONumber r) -> Oratio.equals r h
          | _ -> false) t)
  -> true
| Repeat (Length c1, Aexpr (Abinop (Div,
    PONumber (Oratio.ReducedRatio (1, 1)), 
    Length c2))) when c1 = c2 -> true 
| _ -> false

let is_random_integer ~weights ~choices = match weights, choices with 
| Repeat (Length (Range (min1, max1)), Aexpr (Abinop (Div,
    PONumber (Oratio.ReducedRatio (1,1)), 
    Length (Range (min2, max2))))),
  Range (min3, max3) 
  when min1 = min2 && min2 = min3 && max1 = max2 && max2 = max3 ->
  Some min1, Some max1
| _, _ -> None, None

let rec is_bt_array = function
| [] -> true
| Bexpr (RandomBoolean (_, c, _, _))::t 
| Aexpr (RandomNumber (_, c, _, _))::t
  when is_bernoulli_trial c -> is_bt_array t
| _ -> false 

let rec is_num_array (arr : po_expr list) = match arr with
| [] -> true
| Aexpr _::t -> is_num_array t
| h::t -> false 

let rec is_bool_array = function
| [] -> true
| Bexpr _::t -> is_bool_array t
| _ -> false 

let rec is_str_array = function
| [] -> true
| Sexpr _::t -> is_str_array t
| _ -> false 

let rec is_cont_array = function
| [] -> true
| Cexpr _::t -> is_cont_array t
| _ -> false 

let get_type_of_list l =
if is_bernoulli_trial (POArray (Unknown, l)) || is_bt_array l
then Boolean
else if is_num_array l
then Number
else if is_str_array l
then String
else if is_cont_array l
then Container
else Unknown

let rec is_constant = function
| Phi _ -> false
| Aexpr (PONumber _) 
| Bexpr (POBoolean _)
| Sexpr (POString _)
  -> true
| Cexpr (POArray (t, arr)) ->
  List.for_all is_constant arr
| Cexpr (POMap (t, m)) ->
  List.for_all is_constant (POMap_.bindings m |> List.map snd)
| _ -> false

let is_phi = function Phi _ -> true | _ -> false 

let is_function = function 
| RandomVar _ 
| CustomExpr _
| Iexpr _ 
| Coalesce _ 
| Aexpr (CustomNumber _ )
| Aexpr (RandomNumber _)
| Aexpr (CoalesceNumber _ )
| Aexpr (AIexpr _ )
| Aexpr (Length _ )
| Aexpr (Abinop _ )
| Bexpr (CustomBoolean _ )
| Bexpr (RandomBoolean _)
| Bexpr (CoalesceBoolean _ )
| Bexpr (BIexpr _  )
| Cexpr (CustomContainer _)
| Cexpr (RandomContainer _)
| Cexpr (CoalesceContainer _ )
| Cexpr (CIexpr _ )
| Sexpr (CustomString _ )
| Sexpr (RandomString _)
| Sexpr (CoalesceString _)
| Sexpr (SIexpr _) -> true
| _ -> false

let is_relation = function
| Bexpr (Equals _)
| Bexpr (BinNumOp _)
(* | Bexpr (BinBinOp (BEquals, _, _)) *)
| Bexpr (BinBinOp _)
| Bexpr (BinCtrOp _)
| Bexpr (BinStrOp _) -> true
| _ -> false

let rec is_random_variable = function
| Aexpr (RandomNumber _)
| Aexpr (CustomNumber (_, _, Some _))
| Aexpr (GetNumber (_, Random, _, _))
| Bexpr (RandomBoolean _)
| Bexpr (CustomBoolean (_, _, Some _))
| Bexpr (GetBoolean (_, Random, _, _))
| Cexpr (RandomContainer _)
| Cexpr (CustomContainer (_, _, _, Some _))
| Cexpr (GetContainer (_, Random, _, _, _))
| Sexpr (RandomString _)
| Sexpr (CustomString (_, _, Some _))
| Sexpr (GetString (_, Random, _, _))
| RandomVar _ 
| CustomExpr (_, _, Some _)
| Get (_, Random, _, _) -> true
| _ -> false

let is_null = function
| Null
| Aexpr NullNumber
| Bexpr NullBoolean
| Cexpr NullContainer
| Sexpr NullString
  -> true
| _ -> false 

let rec get_ast_subtree ~find_fn n : ast_node option = match n with 
| Seq (h::t) -> if find_fn h 
  then Some n
  else begin match get_ast_subtree ~find_fn:find_fn h with 
      | Some n' -> Some (Seq (n'::t))
      | None -> get_ast_subtree ~find_fn:find_fn (Seq t)
    end
| Cond ((g, ns)::t) -> if find_fn g || find_fn ns
  then Some n
  else begin match get_ast_subtree ~find_fn:find_fn ns with 
      | Some _ -> Some n (* Don't break up the conditional *)
      | None -> get_ast_subtree ~find_fn:find_fn (Cond t)
    end
| _ -> if find_fn n 
  then Some n 
  else None    

let rec get_sub_expr ?(efn=fun _ -> false) 
                    ?(afn=fun _ -> false)
                    ?(bfn=fun _ -> false)
                    ?(cfn=fun _ -> false)
                    ?(sfn=fun _ -> false) e : po_expr option = 
let rec get_sub_aexpr e =
  if afn e then Some (Aexpr e)
  else match e with 
    | NullNumber
    | PONumber _
    | GetNumber _ 
    | CustomNumber _ 
      -> None 
    | RandomNumber (weights, choices, _, _) ->
      begin match get_sub_cexpr weights with 
        | None -> get_sub_cexpr choices 
        | e' -> e'
      end
    | CoalesceNumber (attempt, default) ->
      begin match get_sub_aexpr attempt with 
        | None -> get_sub_aexpr default 
        | e' -> e' 
      end 
    | AIexpr (base, index) ->
      begin match get_sub_cexpr base with 
        | None -> get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn index
        | e' -> e' 
      end 
    | Length c -> get_sub_cexpr c 
    | Abinop (_, e1, e2) ->
      begin match get_sub_aexpr e1 with 
        | None -> get_sub_aexpr e2 
        | e' -> e'
      end 
and get_sub_bexpr e = 
  if bfn e 
  then Some (Bexpr e)
  else match e with 
    | NullBoolean 
    | POBoolean _ 
    | GetBoolean _ 
    | CustomBoolean _ 
      -> None 
    | RandomBoolean (weights, choices, _, _) ->
      begin match get_sub_cexpr weights with 
        | None -> get_sub_cexpr choices
        | e' -> e'
      end  
    | CoalesceBoolean (attempt, default) ->
      begin match get_sub_bexpr attempt with 
        | None -> get_sub_bexpr default 
        | e' -> e' 
      end 
    | BIexpr (base, index) ->
      begin match get_sub_cexpr base with 
        | None -> get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn index 
        | e' -> e'
      end 
    | Not e -> get_sub_bexpr e
    | Equals (e1, e2) ->
      begin match get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn e1 with 
        | None ->  get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn e2
        | e' -> e' 
      end 
    | BinBinOp (_, e1, e2) -> 
      begin match get_sub_bexpr e1 with 
        | None -> get_sub_bexpr e2 
        | e' -> e' 
      end 
    | BinStrOp (_, e1, e2) ->
      begin match get_sub_sexpr e1 with 
        | None -> get_sub_sexpr e2 
        | e' -> e' 
      end
    | BinCtrOp (_, e1, e2) -> 
      begin match get_sub_cexpr e1 with 
        | None -> get_sub_cexpr e2 
        | e' -> e'
      end 
    | BinNumOp (_, e1, e2) ->
      begin match get_sub_aexpr e1 with 
        | None -> get_sub_aexpr e2 
        | e' -> e'
      end 
and get_sub_cexpr (e : po_cexpr) : po_expr option =
  if cfn e then Some (Cexpr e)
  else match e with 
    | NullContainer 
    | POArray (_, []) 
    | GetContainer _
    | CustomContainer _
    | Range _
      -> None 
    | RandomContainer (weights, choices, _, _) ->
      begin match get_sub_cexpr weights with 
        | None -> get_sub_cexpr choices 
        | e' -> e'
      end 
    | POArray (t, h::tl) ->
      begin match get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn h with
        | None -> get_sub_cexpr (POArray (t, tl))
        | e' -> e'
      end 
    | POMap (t, m) -> 
      get_sub_cexpr (POArray (t, POMap_.bindings m |> List.map snd))
    | CoalesceContainer (attempt, default) ->
      begin match get_sub_cexpr attempt with 
        | None -> get_sub_cexpr default 
        | e' -> e'
      end 
    | CIexpr (base, index) ->
      begin match get_sub_cexpr base with 
        | None -> get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn index 
        | e' -> e'
      end 
    | Repeat (_, e) -> get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn e
    | EnumChoose _ -> assert false 
and get_sub_sexpr e = 
  if sfn e then Some (Sexpr e)
  else match e with 
    | NullString 
    | POString _ 
    | GetString _ 
    | CustomString _ 
      -> None 
    | RandomString (weights, choices, _, _) ->
      begin match get_sub_cexpr weights with 
        | None -> get_sub_cexpr choices 
        | e' -> e' 
      end 
    | CoalesceString (attempt, default) ->
      begin match get_sub_sexpr attempt with 
        | None -> get_sub_sexpr default 
        | e' -> e'
      end 
    | SIexpr (base, index) ->
      begin match get_sub_cexpr base with 
        | None -> get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn index 
        | e' -> e' 
      end 
in 
if efn e 
then Some e 
else match e with 
  | Null 
  | CustomExpr _
  | Get _ 
  | Phi _
    ->  None
  | Aexpr ae -> get_sub_aexpr ae 
  | Bexpr be -> get_sub_bexpr be
  | Cexpr ce -> get_sub_cexpr ce
  | Sexpr se -> get_sub_sexpr se 
  | Coalesce (attempt, default) -> 
    begin match get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn attempt with 
      | None -> get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn default
      | e' -> e'
    end 
  | Iexpr (base, index) ->
    begin match get_sub_cexpr base with 
      | None -> get_sub_expr ~efn ~afn ~bfn ~cfn ~sfn index 
      | e' -> e'
    end 
  | RandomVar (weights, choices, _, _) ->
    begin match get_sub_cexpr weights with 
      | None -> get_sub_cexpr choices 
      | e' -> e'
    end 
    
let infer_var_type ?(match_on_index=true) k (Program p) = 
  let (s', _) = k in 
  let match_if bt s i = 
    if (match_on_index && (s, i) = k) || ((not match_on_index) && s' = s)
    then bt
    else Unknown in 
  let rec infer_var_type_stmt n = match n with 
    | Assignment (_, s, i, e) ->
      if (match_on_index && (s, i) = k) || ((not match_on_index) && s' = s)
      then get_expression_type e
      else infer_var_type_expr e 
    | Seq [] -> Unknown
    | Seq (h::tl) -> 
      let t = infer_var_type_stmt h in 
      if t <> Unknown then t else infer_var_type_stmt (Seq tl)
    | Cond ((g, cons)::conds) -> 
      let t = infer_var_type_stmt g in 
      if t <> Unknown then t 
      else 
        let t' = infer_var_type_stmt cons in 
        if t' <> Unknown then t' else infer_var_type_stmt (Cond conds)
    | Guard e 
    | Return e -> infer_var_type_bexpr e
    | _ -> Unknown
  and infer_var_type_expr e = match e with 
    | Aexpr e -> infer_var_type_aexpr e 
    | Bexpr e -> infer_var_type_bexpr e 
    | Cexpr e -> infer_var_type_cexpr e 
    | Sexpr e -> infer_var_type_sexpr e
    | Coalesce (attempt, default) ->
      let t = infer_var_type_expr attempt in 
      if t <> Unknown then t else infer_var_type_expr default
    | Iexpr (base, index) ->
      let t = infer_var_type_cexpr base in 
      if t <> Unknown then t else infer_var_type_expr index
    | _ -> Unknown
  and infer_var_type_aexpr e = match e with 
    | GetNumber (_, _, s, i) -> match_if Number s i 
    | CoalesceNumber (attempt, default) ->
      let t = infer_var_type_aexpr default in 
      if t = Unknown then infer_var_type_aexpr attempt else t 
    | AIexpr (base, index) -> 
      let t = infer_var_type_cexpr base in 
      if t = Unknown then infer_var_type_expr index else t 
    | Length c -> infer_var_type_cexpr c
    | Abinop (_, e1, e2) -> 
      let t = infer_var_type_aexpr e1 in 
      if t = Unknown then infer_var_type_aexpr e2 else t
    | RandomNumber (weights, choices, _, _) ->
      let t = infer_var_type_cexpr weights in 
      if t <> Unknown then t else infer_var_type_cexpr choices  
    | _ -> Unknown 
  and infer_var_type_bexpr e = match e with 
    | GetBoolean (_, _, s, i) -> match_if Boolean s i 
    | CoalesceBoolean (attempt, default) ->
      let t = infer_var_type_bexpr attempt in 
      if t = Unknown then infer_var_type_bexpr default else t 
    | BIexpr (base, index) ->
      let t = infer_var_type_cexpr base in 
      if t = Unknown then infer_var_type_expr index else t 
    | Not e -> infer_var_type_bexpr e 
    | Equals (e1, e2) -> 
      let t = infer_var_type_expr e1 in 
      if t = Unknown then infer_var_type_expr e2 else t 
    | BinNumOp (_, e1, e2) -> 
      let t = infer_var_type_aexpr e1 in 
      if t = Unknown then infer_var_type_aexpr e2 else t
    | BinBinOp (_, e1, e2) ->
      let t = infer_var_type_bexpr e1 in 
      if t = Unknown then infer_var_type_bexpr e2 else t
    | BinCtrOp (_, e1, e2) ->
      let t = infer_var_type_cexpr e1 in 
      if t = Unknown then infer_var_type_cexpr e2 else t 
    | BinStrOp (_, e1, e2) ->
      let t = infer_var_type_sexpr e1 in 
      if t = Unknown then infer_var_type_sexpr e2 else t 
    | RandomBoolean (weights, choices, _, _) ->
      let t = infer_var_type_cexpr weights in 
      if t <> Unknown then t else infer_var_type_cexpr choices  
    | _ -> Unknown
  and infer_var_type_cexpr e = match e with 
    | GetContainer (_, _, s, i, _) -> match_if Container s i
    | CoalesceContainer (attempt, default) ->
      let t = infer_var_type_cexpr default in 
      if t = Unknown then infer_var_type_cexpr attempt else t
    | RandomContainer (weights, choices, _, _) ->
      let t = infer_var_type_cexpr weights in 
      if t <> Unknown then t else infer_var_type_cexpr choices  
    | _ -> Unknown
  and infer_var_type_sexpr e = match e with 
    | GetString (_, _, s, i) -> match_if String s i
    | CoalesceString (attempt, default) ->
      let t = infer_var_type_sexpr default in 
      if t = Unknown then infer_var_type_sexpr attempt else t
    | RandomString (weights, choices, _, _) ->
      let t = infer_var_type_cexpr weights in 
      if t <> Unknown then t else infer_var_type_cexpr choices  
    | _ -> Unknown
  in infer_var_type_stmt p

let resolve_type e types name = 
    let rec one_of ?(seen=[]) looking_for base = match base with 
      | [] -> seen
      | h::t when List.mem h looking_for && (not (List.mem h seen)) -> 
        one_of looking_for t ~seen:(h::seen)
      | _::t -> one_of looking_for t ~seen in 
    if Types.mem name !types 
    then 
      let these_types = Types.find name !types in 
      (* need to differentiate:
        
          Scenario A;
            foo = 1;
            foo = true;
        
        where the last assignment dominates, versus

          Scenario B:
            foo = 1;
            if (foo) { 
              ...
            }
        where we must simply rewrite.
        *)
      match one_of [String; Container; Number] these_types with 
      | [] -> begin match one_of [Boolean] these_types with 
          | [] -> Unknown
          | [t] -> t 
          | _ -> assert false 
        end
      | [t] -> t
      | t1::t2::_ -> raise (type_error ~expected:t1 ~found:t2 e) 
    else Unknown 

let add_type types name t = 
  let this_type_set = if Types.mem name !types 
    then Types.find name !types 
    else [] in 
  types := Types.add name (t::this_type_set) !types

let rec get_codomain ?(env=Po_env.empty) (e : po_expr) : base_type =  
  let get_codomain = get_codomain ~env in 
  let types = ref Types.empty in
  let resolve_types =       
    List.fold_left (fun _ e -> 
      types := Types.add "tmp" [get_codomain e] !types; 
      resolve_type e types "tmp")
    Unknown in
  match e with 
  | Cexpr cexpr -> 
    begin match cexpr with 
      | NullContainer -> Unknown
      | EnumChoose (samples, _) -> Container
      | POArray (t, _) -> t
      | POMap (t, _) -> t
      | GetContainer (_, _, name, _, t) 
      | CustomContainer (name , _, t, _) -> t
      | RandomContainer (_, choices, _, _) -> get_codomain (Cexpr choices)
      | CoalesceContainer (attempt, default) ->
        let t = get_codomain (Cexpr default) in 
        if t = Unknown then get_codomain (Cexpr attempt) else t
      | CIexpr (POArray (t, arr), _) -> 
        assert (t = Container || t = Unknown); resolve_types arr
      | CIexpr (POMap (_, m), _) -> 
        resolve_types (POMap_.bindings m |> List.map snd)
      | CIexpr _ -> Unknown
      | Range _ -> Number
      | Repeat (_, e) -> get_expression_type e 
    end 
  | Phi (Container, name, ints) -> 
    List.map (fun i -> if Po_env.mem (name, i) env 
                       then Po_env.find (name, i) env
                       else Null) ints 
    |> resolve_types
  | _ -> (* This could be made more precise *) Unknown