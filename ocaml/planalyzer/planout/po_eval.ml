(** Dependencies:
    - Config 
    - Po_aux
    - Po_env
    - Po_syntax
*)
exception NYI of string 
exception IndexCardMismatch of int * int
open Config 
open Po_syntax 

let make_index_card_mismatch ~expected ~is = 
  raise (IndexCardMismatch (expected, is))


let arithfn = function 
  | Sum -> Oratio.add ~reduce:true 
  | Product -> Oratio.multiply ~reduce:true 
  | Mod -> Oratio.modulus 
  | Div -> Oratio.divide

let boolnumfn = function
  | AEquals -> Oratio.equals
  | Gt -> Oratio.gt
  | Lt -> Oratio.lt

let stringfn fn : string -> string -> bool = match fn with 
  | SEquals -> (=)

let containerfn (type t) fn : t list -> t list -> bool = match fn with 
  | CEquals -> (=)

let get_lhs_rhs_eq = function 
  | Equals (e1, e2) -> Some (e1, e2)
  | BinNumOp (AEquals, e1, e2) -> Some (Aexpr e1, Aexpr e2)
  | BinBinOp (BEquals, e1, e2) -> Some (Bexpr e1, Bexpr e2)
  | BinCtrOp (CEquals, e1, e2) -> Some (Cexpr e1, Cexpr e2)
  | BinStrOp (SEquals, e1, e2) -> Some (Sexpr e1, Sexpr e2)
  | _ -> None 


(*****************************************************************************
  Evaluate expressions down as far as we can go.		 
  ****************************************************************************)
let resolve_get (type t) 
  (ctor : origin -> getref -> string -> int -> t) 
  (convert : po_expr -> t) 
  env o m s i : t =
  (* Polymorphic functions get screwed up for recursive definitions: 
  https://blogs.janestreet.com/ensuring-that-a-function-is-polymorphic-in-ocaml-3-12/ *)
  let rec helper ?(steps=0) o m s i = 
    let helper = helper ~steps:(steps + 1) in 
    if steps > (Po_env.bindings env |> List.length) 
    then assert false
    else if o = Config.ExtSource
    then Null
    else if not (Po_env.mem (s, i) env) 
    then Null 
    else begin match Po_env.find (s, i) env with
        | Aexpr (GetNumber (o, m', s', i'))
        | Bexpr (GetBoolean (o, m', s', i')) 
        | Cexpr (GetContainer (o, m', s', i', _))
        | Sexpr (GetString (o, m', s', i')) 
        | Get (o, m', s', i')
          -> helper o m' s' i'
        | e -> if Po_aux.is_constant e then e 
              else if Po_aux.is_random_variable e 
              then Get (o, Random, s, i)
              else if m = Delay || m = Random
              then Get (o, m, s, i) 
              else e  
      end in 
  match helper o m s i with 
    | Get (o, m, s, i) -> ctor o m s i 
    | e -> convert e

let eval_get (type t) (e : t) 
(ctor: origin -> getref -> string -> int -> t)  
(refine: po_expr -> t)
(generalize: t -> po_expr)
eval env : t =
  let update = ref true in 
  let e_prev = ref e in 
  while !update do
    match generalize e with 
    | Get (o, m, s, i)
    | Aexpr (GetNumber (o, m, s, i))
    | Bexpr (GetBoolean (o, m, s, i))
    | Cexpr (GetContainer (o, m, s, i, _))
    | Sexpr (GetString (o, m, s, i)) ->
      let e_next = resolve_get ctor refine env o m s i in 
      if !e_prev = e_next 
      then update := false
      else e_prev := eval env e_next
    | _ -> assert false
  done;
  !e_prev


let get_ctor o m s i = Get (o, m, s, i)
let get_num_ctor o m s i = GetNumber (o, m, s, i)
let get_bool_ctor o m s i = GetBoolean (o, m, s, i)
let get_ctr_ctor t o m s i = GetContainer (o, m, s, i, t)
let get_str_ctor o m s i = GetString (o, m, s, i)

  (** Attempts to reduce the indexing expression to a value. *)
let rec extract_by_key (type b) (ctor : po_cexpr -> po_expr -> b)
                        (convert_fn : po_expr -> b)
                        (base : po_cexpr) (index : po_expr) : b =
  match base, index with
  | POMap (t, m), _ -> 
    begin match index with 
      | Aexpr (PONumber n) -> 
        let s = Oratio.int_of_ratio n |> string_of_int in 
        if POMap_.mem s m 
        then POMap_.find s m |> convert_fn
        else convert_fn Null 
      | Sexpr (POString s) -> 
        if POMap_.mem s m 
        then POMap_.find s m |> convert_fn
        else convert_fn Null 
      | _ -> ctor base index 
    end 
  | POArray (t, arr), Aexpr (PONumber n) ->
    let i = Oratio.int_of_ratio n in
    if i > List.length arr
    then convert_fn Null
    else List.nth arr i |> convert_fn
  | POArray (t, arr), Bexpr (POBoolean b) ->
    let len = List.length arr in 
    if len > 2 
    then raise (make_index_card_mismatch ~expected:len ~is:2)
    else List.nth arr (if b then 1 else 0) |> convert_fn
  | _, _ -> ctor base index


let rec convert_phi_to_coalesce env phi = 
  let convert_phi_to_coalesce = convert_phi_to_coalesce env in 
  match phi with 
  | Phi (t, label, a::b::tl) -> 
    let o = Po_env.get_origin label env in 
    let o1, o2 = o    , if b = 0 then ExtSource else o     in 
    let m1, m2 = Delay, if b = 0 then External  else Delay in 
    begin match t with 
      | Number -> Aexpr (CoalesceNumber (
        GetNumber (o1, m1, label, a),
        if tl = [] 
        then GetNumber (o2, m2, label, b) 
        else convert_phi_to_coalesce (Phi (t, label, b::tl)) |> to_number))
      | Boolean -> Bexpr (CoalesceBoolean (
        GetBoolean (o1, m1, label, a), 
        if tl = [] 
        then GetBoolean (o2, m2, label, b)
        else convert_phi_to_coalesce (Phi (t, label, b::tl)) |> to_boolean))
      | Container -> 
        Cexpr (CoalesceContainer (
        GetContainer (o1, m1, label, a, Unknown), 
        if tl = [] 
        then GetContainer (o2, m2, label, b, Unknown)
        else convert_phi_to_coalesce (Phi (t, label, b::tl)) |> to_container))
      | String -> Sexpr (CoalesceString (
        GetString (o1, m1, label, a), 
        if tl = [] 
        then GetString (o2, m2, label, b)
        else convert_phi_to_coalesce (Phi (t, label, b::tl)) |> to_string))
      | Unknown -> Coalesce (
        Get (o1, m1, label, a), 
        if tl = []
        then Get (o, m2, label, b)
        else convert_phi_to_coalesce (Phi (Unknown, label, b::tl)))
      end 
  | _ -> assert false 
    

(* let eval_coalesce (type t) (ctor : t -> t -> t) (convert : t -> po_expr)
                (attempt : t) (default : t) : t =
  if Po_aux.is_null (convert attempt)
  then default 
  else if Po_aux.is_constant (convert attempt)
  then attempt
  else ctor attempt default *)

let eval_coalesce (type t) (null : t) (convert : t -> po_expr)
                (attempt : t) (default : t) : t =
  if Po_aux.is_null (convert attempt)
  then default 
  else attempt

let rec sort = function
  | Abinop (Sum, e1, e2) ->
    begin match sort e1, sort e2 with
      (* reduce *)
      | PONumber r1, PONumber r2 -> PONumber (Oratio.add r1 r2)
      (* absorb *)
      | PONumber (Oratio.ReducedRatio (0, 1)), e
      | e, PONumber (Oratio.ReducedRatio (0, 1)) -> e
      (* associate *)
      | PONumber r1, Abinop (Sum, PONumber r2, e) 
      | Abinop (Sum, PONumber r2, e), PONumber r1 ->
        Abinop (Sum, PONumber(Oratio.add r1 r2), e)
      (* commute *)
      | PONumber r, e
      | e, PONumber r -> 
        Abinop (Sum, PONumber r, e)
      | e1, Abinop (Sum, PONumber r, e2) 
      | Abinop (Sum, PONumber r, e1), e2 ->
        Abinop (Sum, PONumber r, Abinop (Sum, e1, e2))
      | e1', e2' -> Abinop (Sum, e1', e2')
    end
  | Abinop (Product, e1, e2) ->
    begin match sort e1, sort e2 with
      (* reduce *)
      | PONumber r1, PONumber r2 -> PONumber (Oratio.multiply r1 r2)
      (* absorb *)
      | PONumber (Oratio.ReducedRatio (1, 1)), e
      | e, PONumber (Oratio.ReducedRatio (1, 1)) -> e 
      (* distribute *)
      (* One expr is symbolic only if at least one of its terms is symbolic. 
          If exactly one term is symbolic, it will be the right; the left will 
          be concrete. We can distribute if the left is concrete. Otherwise, 
          no change. *)
      | PONumber r1, Abinop (op, PONumber r2, e2) 
      | Abinop (op, PONumber r2, e2), PONumber r1 
        when op = Sum || op = Product ->
        Abinop (op, PONumber (Oratio.multiply r1 r2), e2)
      (* commute *)
      | e, PONumber r1 
      | PONumber r1, e ->
        Abinop (Product, PONumber r1, e)
      | e1', e2' -> Abinop (Product, e1', e2')
    end 
  | Abinop (Div, e1, e2) ->
    begin match sort e1, sort e2 with 
      (* reduce *)
      | PONumber r1, PONumber r2 -> PONumber (Oratio.divide r1 r2)
      (* distribute, normalize *)
      | Abinop (Sum, e1, e2), denom -> 
        sort (Abinop (Sum, Abinop (Div, e1, denom), Abinop (Div, e2, denom)))
      | Abinop (Product, e1, e2), denom ->
        sort (Abinop (Product, Abinop (Div, e1, denom), e2))
      | Abinop (Div, e1, e2), denom ->
        sort (Abinop (Div, Abinop (Product, e1, denom), e2))
      (* commute *)
      | e, PONumber r1
      | PONumber r1, e ->
        Abinop (Product, PONumber r1, e)
      | e1', e2' -> Abinop (Div, e1', e2')
    end
  | Abinop (Mod, e1, e2) ->
    begin match sort e1, sort e2 with 
      (* reduce *)
      | PONumber r1, PONumber r2 -> PONumber (Oratio.modulus r1 r2)
      | e1', e2' -> Abinop (Mod, e1', e2')
    end 
  | e -> e

let rec reduce_bool expr env = match expr with 
  | NullBoolean 
  | BinBinOp (And, POBoolean false, _)
  | BinBinOp (And, _, POBoolean false) 
  | Not (POBoolean true)
  | POBoolean false
      -> POBoolean false
    
  | BinBinOp (Or, POBoolean true, _)
  | BinBinOp (Or, _, POBoolean true)
  | Not (POBoolean false)
  | POBoolean true
    -> POBoolean true

  | Not e ->
    let e' = reduce_bool e env in 
    if e' = e then expr else reduce_bool (Not e') env 

  | BinBinOp (And, e1, e2) as expr ->
      begin 
        match reduce_bool e1 env, reduce_bool e2 env with
        | POBoolean true, POBoolean true -> POBoolean true
        | POBoolean false, _ | _, POBoolean false -> POBoolean false
        | POBoolean true, e | e, POBoolean true -> e
        | _ -> expr
      end

  | BinBinOp (Or, e1, e2) as expr ->
      begin
        match reduce_bool e1 env, reduce_bool e2 env with
        | POBoolean false, POBoolean false -> POBoolean false
        | POBoolean true, _ | _, POBoolean true -> POBoolean true
        | POBoolean false, e | e, POBoolean false -> e
        | _ -> expr
      end

  | Equals (e1, e2) as e -> if e1 = e2 then POBoolean true else e
  | BinBinOp (BEquals, e1, e2) as e -> if e1 = e2 then POBoolean true else e
  | BinStrOp (SEquals, e1, e2) as e -> if e1 = e2 then POBoolean true else e
  | BinCtrOp (CEquals, e1, e2) as e -> if e1 = e2 then POBoolean true else e

  | BinNumOp (AEquals, e1, e2) as e ->
    begin 
      match e1, e2 with 
      | PONumber n1, PONumber n2 -> 
        POBoolean (Oratio.equals n1 n2)
      | PONumber n, NullNumber
      | NullNumber, PONumber n -> 
        POBoolean (n = Oratio.zero) 
      | _ -> e 
    end

  | e -> e

let normalize_weights (weights : po_cexpr) : po_cexpr = match weights with
  | POArray (_, arr) ->
    let arr_num = List.map to_number arr in 
    let sum = List.fold_left (fun a b -> Abinop (Sum, a, b)) 
                              (PONumber Oratio.zero) 
                              arr_num in 
    POArray (Number, List.map (fun w -> Aexpr (Abinop (Div, w, sum))) arr_num)
  | _ -> weights

let rec eval_po_expr env e : po_expr = match e with 
  | Phi (_, label, ints) ->
      assert (List.length ints > 1);
      (* let ints = List.sort compare ints |> List.rev in *)
      eval_po_expr env (convert_phi_to_coalesce env e)
  | Null -> e
  | Aexpr e -> Aexpr (eval_po_aexpr env e)
  | Bexpr e -> Bexpr (eval_po_bexpr env e)
  | Cexpr e -> Cexpr (eval_po_cexpr env e)
  | Sexpr e -> Sexpr (eval_po_sexpr env e)
  | CustomExpr (name, kvlist, salt) ->
      CustomExpr (name,
      List.combine (List.map fst kvlist)
            (List.map snd kvlist |> List.map (eval_po_expr env)), 
            salt)
  | RandomVar (weights, choices, unit, salt) ->
    eval_rv env weights choices unit salt
  | Iexpr (base, index) -> 
    let ctor base index = Iexpr (base, index) in 
    let base' = eval_po_cexpr env base in 
    let index' = eval_po_expr env index in 
    extract_by_key ctor Utils.identity base' index'
  | Coalesce (e1, e2) -> 
    let attempt = eval_po_expr env e1 in
    let default = eval_po_expr env e2 in 
    (* let ctor attempt default = Coalesce (attempt, default) in  *)
    eval_coalesce Null Utils.identity attempt default
  | Get (_, External, _, _) 
  | Get (ExtSource, _, _, _) 
    -> e
  | Get _ -> 
    let ctor o m s i = Get (o, m, s, i) in 
    eval_get e ctor Utils.identity Utils.identity eval_po_expr env 
and eval_po_aexpr env (e : po_aexpr) : po_aexpr = match e with 
  | NullNumber 
  | PONumber _
  | GetNumber (_, External, _, _) 
  (* | GetNumber (ExtSource, _, _, _)  *)
    -> e
  | Length c -> begin 
    let open Oratio in 
    match eval_po_cexpr env c with
    | NullContainer -> PONumber (ratio_of_int 0)
    | EnumChoose _ -> raise (NYI "numeric sample")
    | CustomContainer _ as cont -> Length cont
    | RandomContainer (weights, _, _, _) ->
      eval_po_aexpr env (Length (CIexpr (weights, Aexpr (PONumber zero))))
    | POArray (_, arr) -> PONumber (List.length arr |> ratio_of_int)
    | POMap (_, m)  -> PONumber (POMap_.cardinal m |> ratio_of_int)
    | GetContainer (o, External, _, _, _)
    | GetContainer (o, Delay, _, _, _)
    | GetContainer (o, Random, _, _, _) as c' -> Length c'
    | GetContainer (o, Unclassified, s, i, t) as e ->
        if Po_env.mem (s, i) env
        then
          (*let ctor o m s i = GetContainer (o, m, s, i, t) in *)
          let ctor o m s i = Get (o, m, s, i) in 
          let resolved = 
            eval_get (Cexpr e) ctor Utils.identity Utils.identity 
              eval_po_expr env in 
            (*resolve_get ctor Utils.identity env Unclassified s i in*)
          if Po_aux.is_random_variable resolved
          then Length (GetContainer (o, Random, s, i, t))
          else if Po_aux.is_function resolved 
          then Length (GetContainer (o, Delay, s, i, t))
          else Length (to_container resolved)
        else Length (GetContainer (o, External, s, i, t))
      | CIexpr _ -> raise (NYI "numeric indexing")
      | CoalesceContainer _ -> raise (NYI "numeric coalesce")
      | Repeat (num_times, _) -> num_times
      | Range (min, max) ->
        let neg_min = Abinop (Product, PONumber neg_one, min) in
        let diff = Abinop (Sum, max, neg_min) in
        Abinop (Sum, PONumber one, diff)
    end
  | AIexpr (base, index) ->
    let ctor base index = AIexpr (base, index) in 
    let base' = eval_po_cexpr env base in 
    let index' = eval_po_expr env index in 
    extract_by_key ctor to_number base' index'
  | GetNumber (_, m, s, i) -> 
    let ctor o m s i = GetNumber (o, m, s, i) in 
    eval_get e ctor to_number from_number eval_po_aexpr env 
  | CustomNumber (name, kvlist, salt) ->
    CustomNumber (name, 
      List.map (fun (k, v) -> (k, eval_po_expr env v)) kvlist,
      salt)
  | RandomNumber (weights, choices, u, s) ->
    RandomNumber (eval_po_cexpr env weights, eval_po_cexpr env choices, u, s)
  | CoalesceNumber (e1, e2) ->
    (* let ctor attempt default = CoalesceNumber (attempt, default) in  *)
    let attempt = eval_po_aexpr env e1 in 
    let default = eval_po_aexpr env e2 in 
    eval_coalesce NullNumber from_number attempt default
  | Abinop (op, e1, e2) ->
    let e1', e2' = eval_po_aexpr env e1, eval_po_aexpr env e2 in
      begin match e1', e2' with 
        | PONumber n1, PONumber n2 -> PONumber (arithfn op n1 n2)
        | _ -> sort (Abinop (op, e1', e2'))
      end
and eval_po_bexpr env e = match e with 
  | NullBoolean
  | POBoolean _
  | GetBoolean (_, External, _, _)
  (* | GetBoolean (ExtSource, _, _, _)  *)
    as e -> e
  | CustomBoolean (name, kvlist, salt) ->
    CustomBoolean (name, 
      List.map (fun (k, v) -> (k, eval_po_expr env v)) kvlist,
      salt)
  | RandomBoolean (weights, choices, u, s) ->
    RandomBoolean (eval_po_cexpr env weights, eval_po_cexpr env choices, u, s)
  | CoalesceBoolean (attempt, default) ->
    let evaled_attempt = eval_po_bexpr env attempt in
    let evaled_default = eval_po_bexpr env default in
    (* let ctor attempt default = CoalesceBoolean (attempt, default) in  *)
    eval_coalesce NullBoolean from_boolean evaled_attempt evaled_default
  | BinStrOp (op, e1, e2) ->
    begin match eval_po_sexpr env e1, eval_po_sexpr env e2 with 
      | POString s1, POString s2 -> POBoolean (stringfn op s1 s2 )
      | e1', e2' -> BinStrOp(SEquals, e1', e2')
    end
  | BinCtrOp (op, e1, e2) ->
    begin match eval_po_cexpr env e1, eval_po_cexpr env e2 with 
      | POArray (_, arr1), POArray (_, arr2) -> 
        POBoolean (containerfn op arr1 arr2)
      | POMap (_, m1), POMap (_, m2) -> 
        POBoolean (containerfn op (POMap_.bindings m1) (POMap_.bindings m2)) 
      | e1', e2' -> BinCtrOp (op, e1', e2')
    end
  | Equals (e1, e2) -> Equals (eval_po_expr env e1, eval_po_expr env e2)
  | BinBinOp (op, e1, e2) ->
    let e1' = eval_po_bexpr env e1 in
    let e2' = eval_po_bexpr env e2 in
    begin match op with
      | And -> begin match e1', e2' with
                  | POBoolean true, POBoolean true -> POBoolean true
                  | POBoolean false, _ | _, POBoolean false -> POBoolean false
                  | POBoolean true, e | e, POBoolean true -> e
                  | _, _ -> BinBinOp (And, e1', e2')
                end
      | Or -> begin match e1', e2' with
                | POBoolean false, POBoolean false -> POBoolean false
                | POBoolean true, _ | _, POBoolean true -> POBoolean true
                | POBoolean false, e | e, POBoolean false -> e
                | _, _ -> BinBinOp (Or, e1', e2')
              end
      | BEquals -> begin match e1', e2' with
                      | POBoolean true, POBoolean true  
                      | POBoolean false, POBoolean false -> POBoolean true
                      | POBoolean true, POBoolean false 
                      | POBoolean false, POBoolean true  -> POBoolean false
                      | _ , _ -> BinBinOp(BEquals, e1', e2')
                    end
    end
  | Not e -> reduce_bool (Not (eval_po_bexpr env e)) env
  | GetBoolean (_, m, s, i) ->
    let ctor o m s i = GetBoolean (o, m, s, i) in 
    eval_get e ctor to_boolean from_boolean eval_po_bexpr env 
  | BIexpr (base, index) ->
    let ctor base index = BIexpr (base, index) in 
    let base' = eval_po_cexpr env base in 
    let index' = eval_po_expr env index in 
    extract_by_key ctor to_boolean base' index'
  | BinNumOp (op, e1, e2) ->
    match eval_po_aexpr env e1, eval_po_aexpr env e2 with
    | PONumber r1, PONumber r2 -> POBoolean (boolnumfn op r1 r2) 
    | e1', e2' -> BinNumOp (op, e1', e2')
and eval_po_cexpr env (e: po_cexpr) : po_cexpr = match e with 
  | NullContainer 
  | GetContainer (_, External, _, _, _)
  (* | GetContainer (ExtSource, _, _, _, _)  *)
    -> e
  | CoalesceContainer(attempt, default) ->       
    let evaled_attempt = eval_po_cexpr env attempt in
    let evaled_default = eval_po_cexpr env default in
    (* let ctor attempt default = CoalesceContainer (attempt, default) in  *)
    eval_coalesce NullContainer from_container evaled_attempt evaled_default
  | POArray (t, arr) -> POArray (t, List.map (eval_po_expr env) arr)
  | GetContainer (o, m, s, i, t) ->
    let ctor o m s i = GetContainer (o, m, s, i, t) in 
    eval_get e ctor to_container from_container eval_po_cexpr env
  | CustomContainer (name, kvlist, t, salt) -> 
    CustomContainer (name, 
      List.map (fun (k, v) -> (k, eval_po_expr env v)) kvlist, 
      t, salt)
  | RandomContainer (weights, choices, u, s) ->
    RandomContainer (eval_po_cexpr env weights, eval_po_cexpr env choices, u, s)
  | CIexpr (base, index) ->
    let ctor base index = CIexpr (base, index) in 
    let base' = eval_po_cexpr env base in 
    let index' = eval_po_expr env index in 
    extract_by_key ctor to_container base' index'
  | POMap (t, m) -> POMap (t, POMap_.map (eval_po_expr env) m)
  | Range (min, max) ->
    begin match eval_po_aexpr env min, eval_po_aexpr env max with
      | PONumber r1, PONumber r2 ->
        let min' = Oratio.int_of_ratio r1 in 
        let max' = Oratio.int_of_ratio r2 in 
        let diff = max' - min' in 
        let range = Utils.range (diff + 1)
                    |> List.map ((+) min')
                    |> List.rev in
        POArray (Number, 
          List.map (fun n -> 
            (Aexpr (PONumber (Oratio.ratio_of_int n)))) range)
      | min', max' -> Range(min', max')
    end
  | Repeat (n, item) ->
    begin match eval_po_aexpr env n, eval_po_expr env item with
      | PONumber r, item' ->
        let n' = Oratio.int_of_ratio r in
        POArray (Po_aux.get_expression_type item',
                  List.map (fun _ -> item') (Utils.range n'))
      | n', item' ->
        Repeat (n', item')
    end
  | EnumChoose (choices, num_samples) ->
    let choices' = eval_po_cexpr env choices in
    let num_samples' = eval_po_aexpr env num_samples in
    EnumChoose (choices', num_samples')
and eval_po_sexpr env e = match e with  
  | NullString
  | POString _
  | GetString (_, External, _, _)
  (* | GetString (ExtSource, _, _, _)  *)
      -> e
  | GetString (o, m, s, i) ->
    let ctor o m s i = GetString (o, m, s, i) in 
    eval_get e ctor to_string from_string eval_po_sexpr env 
  | CustomString (name, kvlist, salt) ->
    let (names, values) = List.split kvlist in
    CustomString (name, 
      List.combine names (List.map (eval_po_expr env) values),
      salt)
  | RandomString (weights, choices, u, s) ->
    RandomString (eval_po_cexpr env weights, eval_po_cexpr env choices, u, s)
  | CoalesceString (attempt, default) ->
    let evaled_attempt = eval_po_sexpr env attempt in
    let evaled_default = eval_po_sexpr env default in
    (* let ctor attempt default = CoalesceString (attempt, default) in  *)
    eval_coalesce NullString from_string evaled_attempt evaled_default
  | SIexpr (base, index) ->
    let ctor base index = SIexpr (base, index) in 
    let base' = eval_po_cexpr env base in 
    let index' = eval_po_expr env index in 
    extract_by_key ctor to_string base' index'
and eval_rv env weights choices unit salt = 
  let weights' = eval_po_cexpr env weights 
                  |> normalize_weights 
                  |> eval_po_cexpr env in 
  let choices' = eval_po_cexpr env choices in
  RandomVar (weights', choices', unit, salt)

