(** Dependencies:
    - Po_aux 
    - Po_kwd
    - Po_syntax
*)
exception Print_exception
open Printf 
open Po_syntax

let indent = "  "

let bernoulli_format = format_of_string 
  "bernoulliTrial(p=%s, unit=%s, salt=%s)"
let uniform_format = format_of_string 
  "uniformChoice(choices=%s, unit=%s, salt=%s)"
let weighted_format = format_of_string 
  "weightedChoice(weights=%s, choices=%s, unit=%s, salt=%s)"
let random_integer_format = format_of_string 
  "randomInteger(min=%s, max=%s, unit=%s, salt=%s)"

let string_of_origin o = Config.show_origin o |> sprintf "%s"
let string_of_getref m = show_getref m |> sprintf "%s"

let string_of_program ?(show_index=false) (Program p) =
  (* let line_num = ref 1 in  *)
  let rec string_of_custom ?(show_index=false) name kvlist unit =
    let unit_str = match unit with 
      | None -> empty_string
      | Some {unit_arg; unit_value; salt} -> 
        sprintf "%s=%s, salt=%s" 
          unit_arg 
          (string_of_po_uexpr unit_value) 
          (string_of_po_sexpr salt) in 
    if List.length kvlist = 0
    then sprintf "%s(%s)" name unit_str 
    else 
      sprintf (if unit_str = empty_string then "%s(%s%s)" else "%s(%s, %s)") 
        name
        (Utils.join ", "
              (fun (k, v) -> sprintf "%s=%s" k (string_of_po_expr v)) 
              kvlist)
        unit_str
  and string_of_get show_index m s i =
    sprintf "%s%s" s (if show_index then sprintf "_%d" i else empty_string)
  and string_of_abinop = function
    | Sum -> Po_kwd.sum_sym
    | Product -> Po_kwd.product_sym
    | Mod -> Po_kwd.dom
    | Div -> Po_kwd.div
  and string_of_binnumop = function
    | AEquals -> Po_kwd.equals_sym
    | Lt -> Po_kwd.lt
    | Gt -> Po_kwd.gt
  and string_of_binbinop = function
    | And -> Po_kwd.dna_sym
    | Or -> Po_kwd.or_sym
    | BEquals -> Po_kwd.equals_sym
  and string_of_binstrop = function
    | SEquals -> Po_kwd.equals_sym
  and string_of_binctrop = function
    | CEquals -> Po_kwd.equals_sym
  and string_of_random_variable weights choices unit salt = 
    let unit_str = (string_of_po_uexpr unit) in
    let salt_str = string_of_po_sexpr ~show_index:show_index salt in     
    if Po_aux.is_bernoulli_trial choices
    then sprintf bernoulli_format  
      (string_of_bernoulli_weights show_index weights) unit_str salt_str
    else match Po_aux.is_random_integer weights choices with 
      | Some min, Some max -> sprintf random_integer_format 
        (string_of_po_aexpr min) (string_of_po_aexpr max) unit_str salt_str
      | _, _ ->
      let choices_str = string_of_po_cexpr ~show_index:show_index choices in
      let weights_str = string_of_po_cexpr ~show_index:show_index weights in
      if Po_aux.is_uniform_choice weights
      then sprintf uniform_format choices_str unit_str salt_str
      else sprintf weighted_format weights_str choices_str unit_str salt_str 
  and string_of_po_expr ?(show_index=false) = function
    | Aexpr e -> string_of_po_aexpr ~show_index:show_index e
    | Bexpr e -> string_of_po_bexpr ~show_index:show_index e
    | Cexpr e -> string_of_po_cexpr ~show_index:show_index e
    | Sexpr e -> string_of_po_sexpr ~show_index:show_index e
    | Null -> "null"
    | Get (o, m, s, i)  -> string_of_get show_index m s i
    | CustomExpr (name, kvlist, unit) -> string_of_custom name kvlist unit
    | RandomVar (weights, choices, unit, salt) ->
      string_of_random_variable weights choices unit salt
    | Coalesce (e1, e2) ->
      sprintf "coalesce(%s, %s)"
              (string_of_po_expr ~show_index:show_index e1)
              (string_of_po_expr ~show_index:show_index e2)
    | Iexpr (b, i) ->
      sprintf "%s[%s]"
              (string_of_po_cexpr ~show_index:show_index b)
              (string_of_po_expr ~show_index:show_index i)
    | Phi (_, label, index_lst) ->
      if show_index
      then sprintf "(|)(%s)"  
        (Utils.join ", " (fun i -> sprintf "%s_%d" label i) index_lst)
      else empty_string
  and string_of_po_aexpr ?(show_index=false) = function
    | NullNumber -> if show_index then "null@num" else "null"
    | PONumber n -> Oratio.string_of_ratio n
    | GetNumber (o, m, s, i) -> string_of_get show_index m s i 
    | CustomNumber (name, kvlist, unitr) -> string_of_custom name kvlist unitr
    | RandomNumber (weights, choices, unit, salt) ->
      string_of_random_variable weights choices unit salt
    | CoalesceNumber (e1, e2)->
      sprintf "coalesce(%s, %s)"
              (string_of_po_aexpr ~show_index:show_index e1)
              (string_of_po_aexpr ~show_index:show_index e2)
    | AIexpr (b, i) ->
      sprintf "%s[%s]"
              (string_of_po_cexpr ~show_index:show_index b)
              (string_of_po_expr ~show_index:show_index i)
    | Abinop (op, e1, e2) ->
      sprintf "(%s %s %s)"
              (string_of_po_aexpr ~show_index:show_index e1)
              (string_of_abinop op)
              (string_of_po_aexpr ~show_index:show_index e2)
    | Length e ->
      sprintf "length(%s)" (string_of_po_cexpr ~show_index:show_index e)
  and string_of_po_bexpr ?(show_index=false) : po_bexpr -> string = function
    | NullBoolean -> if show_index then "null@bool" else "null"
    | POBoolean b -> sprintf "%s" (string_of_bool b)
    | GetBoolean (o, m, s, i) -> string_of_get show_index m s i
    | CustomBoolean (name, kvlist, unitr) ->
      string_of_custom name kvlist unitr
    | RandomBoolean (weights, choices, unit, salt) ->
      string_of_random_variable weights choices unit salt
    | CoalesceBoolean (attempt, default) ->
      sprintf "coalesce(%s, %s)"
              (string_of_po_bexpr ~show_index:show_index attempt)
              (string_of_po_bexpr ~show_index:show_index  default)
    | BIexpr (b, i) ->
      sprintf "%s[%s]"
              (string_of_po_cexpr ~show_index:show_index b)
              (string_of_po_expr ~show_index:show_index i)
    | Not e ->
      sprintf "!(%s)" (string_of_po_bexpr ~show_index:show_index e)
    | Equals (e1, e2) ->
      sprintf "(%s == %s)" (string_of_po_expr ~show_index:show_index e1) 
      (string_of_po_expr ~show_index:show_index e2)
    | BinBinOp (op, e1, e2) ->
      sprintf "(%s %s %s)" (string_of_po_bexpr ~show_index:show_index e1) 
      (string_of_binbinop op) (string_of_po_bexpr ~show_index:show_index e2)
    | BinStrOp (op, e1, e2) ->
      sprintf "(%s %s %s)" (string_of_po_sexpr ~show_index:show_index e1) 
      (string_of_binstrop op) (string_of_po_sexpr ~show_index:show_index e2)
    | BinCtrOp (op, e1, e2) ->
      sprintf "(%s %s %s)" (string_of_po_cexpr ~show_index:show_index e1) 
      (string_of_binctrop op) (string_of_po_cexpr ~show_index:show_index e2)
    | BinNumOp (op, e1, e2) ->
      sprintf "(%s %s %s)" (string_of_po_aexpr ~show_index:show_index e1) 
      (string_of_binnumop op) (string_of_po_aexpr ~show_index:show_index e2)
  and string_of_po_cexpr ?(show_index=false)  = function
    | NullContainer -> if show_index then "null@cont" else "null"
    | POArray (_, arr) -> sprintf "[%s]" 
      (Utils.join ", " (string_of_po_expr ~show_index:show_index) arr)
    | POMap (_, m) ->
      let string_of_entry (k, v) = 
        let vstring = string_of_po_expr ~show_index:show_index v in 
        let k = if String.contains k '"' then "opaque-key" else k in 
        let v = if String.contains vstring '"' then "opaque-value" else vstring in 
        sprintf "\"%s\" -> %s" k v in
      POMap_.bindings m
      |> Utils.join ", " string_of_entry 
      |> sprintf "{ %s }"
    | GetContainer (o, m, s, i, _) -> string_of_get show_index m s i
    | CustomContainer (name, kvlist, _, unitr) ->
      string_of_custom name kvlist unitr
    | RandomContainer (weights, choices, unit, salt) ->
      string_of_random_variable weights choices unit salt
    | CoalesceContainer (attempt, default) ->
      sprintf "coalesce(%s, %s)"
              (string_of_po_cexpr ~show_index:show_index attempt)
              (string_of_po_cexpr ~show_index:show_index default)
    | CIexpr (b, i) ->
      sprintf "%s[%s]"
              (string_of_po_cexpr ~show_index:show_index b)
              (string_of_po_expr ~show_index:show_index i)
    | Range (min, max) ->
      sprintf "range(%s, %s)"
              (string_of_po_aexpr ~show_index:show_index min)
              (string_of_po_aexpr ~show_index:show_index max)
    | Repeat (n, item) ->
      sprintf "repeat(%s, %s)"
              (string_of_po_aexpr ~show_index:show_index n)
              (string_of_po_expr ~show_index:show_index item)
    | EnumChoose (choices, sample_size) ->
      sprintf "choose(%s, %s)"
              (string_of_po_cexpr ~show_index:show_index choices)
              (string_of_po_aexpr ~show_index:show_index sample_size)
  and string_of_po_sexpr ?(show_index=false) = function
    | NullString -> if show_index then "null@str" else "null"
    | POString s -> 
      sprintf "\"%s\"" s
    | GetString (o, m, s, i) -> string_of_get show_index m s i
    | CustomString (name, kvlist, unitr) ->
      string_of_custom name kvlist unitr
    | RandomString (weights, choices, unit, salt) ->
      string_of_random_variable weights choices unit salt
    | CoalesceString (attempt, default) ->
      sprintf "coalesce(%s, %s)"
              (string_of_po_sexpr ~show_index:show_index attempt)
              (string_of_po_sexpr ~show_index:show_index default)
    | SIexpr (b, i) ->
      sprintf "%s[%s]"
              (string_of_po_cexpr ~show_index:show_index b)
              (string_of_po_expr ~show_index:show_index i)
  and string_of_po_uexpr : po_uexpr -> string = function
    | Userid -> "userid"
    | Id s -> s ^ "id"
    | UnitR s -> s
    | UExpr e -> (string_of_po_expr e)
    | Tuple2 (u1, u2) ->
      sprintf "(%s, %s)" (string_of_po_uexpr u1) (string_of_po_uexpr u2)
    | Tuple3 (u1, u2, u3) ->
      sprintf "(%s, %s, %s)" (string_of_po_uexpr u1) (string_of_po_uexpr u2) (string_of_po_uexpr u3)
    | Tuple4 (u1, u2, u3, u4) ->
      sprintf "(%s, %s, %s, %s)" (string_of_po_uexpr u1) (string_of_po_uexpr u2) (string_of_po_uexpr u3) (string_of_po_uexpr u4) 
  and string_of_bernoulli_weights show_index = function
    | POArray (_, [_; p]) -> (string_of_po_expr p)
    | GetContainer (o, m, s, i, _) -> string_of_get show_index m s i
    | CIexpr (base, index) -> sprintf "%s[%s]"
              (string_of_po_cexpr base)
              (string_of_po_expr index)
    | _ -> raise Print_exception
  and string_of_ast_node ?(show_index=false) ?(seq_prefix=empty_string) n =
    match n with 
    | Skip _ -> empty_string
    | Expr e -> string_of_po_expr e
    | Seq seqs ->
      (if List.length seqs = 0
       then empty_string 
       else Utils.join "\n" (fun n -> 
         (match n with 
          | Cond _ -> empty_string 
          | _ -> seq_prefix) ^ (string_of_ast_node ~seq_prefix n)) seqs)
    | Assignment (o, label, i, value) ->
      begin
        if not show_index && Po_aux.is_phi value 
        then empty_string 
        else sprintf "%s = %s;"
            (label ^ 
              (if show_index 
               then (string_of_int i |> (^) "_") 
               else empty_string))
            (string_of_po_expr value)
      end
    | Return s ->
      sprintf "return %s;" (string_of_po_bexpr s)
    | Guard b -> string_of_po_bexpr b
    | Cond stmts ->
      let (guards, cons) = List.split stmts in
      let guard_strs = List.map string_of_ast_node guards in
      let new_seq_prefix = seq_prefix ^ "  " in 
      let string_of_if (g, s) = sprintf "(%s) {\n%s\n%s} " g s seq_prefix in
      let con_strs = cons
        |> List.map (string_of_ast_node ~seq_prefix:new_seq_prefix) in 
      List.combine guard_strs con_strs
      |> List.map string_of_if
      |> Utils.join "else if" Utils.identity
      |> (fun s -> "\n" ^ seq_prefix ^ "if " ^ s) in 
  string_of_ast_node ~show_index p

let string_of_expr ?(show_index=false) e = 
  string_of_program ~show_index (Program (Expr e))

let ast_string_of_rand rand = match rand with 
  | None -> "None" 
  | Some rand_info -> show_rand_info rand_info |> sprintf "Some (%s)" 

let ast_string_of_expr e = show_po_expr e |> sprintf "%s"
let ast_string_of_program p = show_program p |> sprintf "%s"