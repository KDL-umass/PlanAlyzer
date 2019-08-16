(** Dependencies: 
    - oratio
    - po_basetypes 
*)
open Oratio
include Po_basetypes

module POMap_ = Map.Make(String) 

type abinop = Sum | Product | Mod | Div [@@deriving show]
type binnumop = AEquals | Lt | Gt       [@@deriving show]
type binbinop = And | Or | BEquals      [@@deriving show]
type binstrop = SEquals                 [@@deriving show]
type binctrop = CEquals                 [@@deriving show]
				  
type getref = 
  | External 
  | Random 
  | Delay 
  | Unclassified  
  [@@deriving show]

type kvlist = (string * po_expr) list 

and rand_info = {
    unit_arg: string; 
    unit_value: po_uexpr; 
    salt: po_sexpr 
  } 

and po_aexpr =
  | NullNumber
  | PONumber             of ratio
  | GetNumber            of Config.origin * getref * string * int
  | CustomNumber         of string * kvlist * rand_info option 
  | RandomNumber         of po_cexpr * po_cexpr * po_uexpr * po_sexpr
  | CoalesceNumber       of po_aexpr * po_aexpr
  | AIexpr               of po_cexpr * po_expr
  | Length               of po_cexpr
  | Abinop               of abinop * po_aexpr * po_aexpr
				    
 and po_bexpr =
   | NullBoolean
   | POBoolean           of bool
   | GetBoolean          of Config.origin * getref * string * int
   | CustomBoolean       of string * kvlist * rand_info option 
   | RandomBoolean       of po_cexpr * po_cexpr * po_uexpr * po_sexpr
   | CoalesceBoolean     of po_bexpr * po_bexpr
   | BIexpr              of po_cexpr * po_expr
   | Not                 of po_bexpr
   | Equals              of po_expr * po_expr
   | BinBinOp            of binbinop * po_bexpr * po_bexpr
   | BinStrOp            of binstrop * po_sexpr * po_sexpr
   | BinCtrOp            of binctrop * po_cexpr * po_cexpr
   | BinNumOp            of binnumop * po_aexpr * po_aexpr

 and po_sexpr =
   | NullString
   | POString            of string
   | GetString           of Config.origin * getref * string * int
   | CustomString        of string * kvlist * rand_info option 
   | RandomString        of po_cexpr * po_cexpr * po_uexpr * po_sexpr
   | CoalesceString      of po_sexpr * po_sexpr
   | SIexpr              of po_cexpr * po_expr

 and po_cexpr =
   | NullContainer
   | POArray             of base_type * po_expr list
   | POMap               of base_type * (po_expr POMap_.t [@opaque])
   | GetContainer        of Config.origin * getref * string * int * base_type
   | CustomContainer     of string * kvlist * base_type * rand_info option 
   | RandomContainer     of po_cexpr * po_cexpr * po_uexpr * po_sexpr
   | CoalesceContainer   of po_cexpr * po_cexpr
   | CIexpr              of po_cexpr * po_expr
   | Range               of po_aexpr * po_aexpr
   | Repeat              of po_aexpr * po_expr
   | EnumChoose          of po_cexpr * po_aexpr
				
 and po_uexpr =
   | Userid
   | Id                  of string
   | UnitR               of string
   | UExpr               of po_expr 
   | Tuple2              of po_uexpr * po_uexpr
   | Tuple3              of po_uexpr * po_uexpr * po_uexpr
   | Tuple4              of po_uexpr * po_uexpr * po_uexpr * po_uexpr
						  
 and po_expr =
   | Null
   | Aexpr                of po_aexpr
   | Bexpr                of po_bexpr
   | Cexpr                of po_cexpr
   | Sexpr                of po_sexpr
   | CustomExpr           of string * kvlist * rand_info option 
   | Get                  of Config.origin * getref * string * int
   | Coalesce             of po_expr * po_expr
   | Iexpr                of po_cexpr * po_expr
   | RandomVar            of po_cexpr * po_cexpr * po_uexpr * po_sexpr 
   | Phi                  of base_type * string * int list 

 and ast_node =
   | Skip                 of string
   | Seq                  of ast_node list
   | Guard                of po_bexpr
   | Cond                 of (ast_node * ast_node) list
   | Assignment           of Config.origin * string * int * po_expr
   | Return               of po_bexpr
   | Expr                 of po_expr
[@@deriving show] 

let empty_string = ""
let po_empty_string = POString empty_string 

exception TypeError of base_type * base_type * po_expr

let type_error ~expected ~found expr= 
  raise (TypeError (expected, found, expr))

type program =
  | Program of ast_node
[@@deriving show]

exception NotFinal of po_expr

let to_type (type a)
            (t_null: a) 
            ~(afn : po_aexpr -> a)
            ~(bfn: po_bexpr -> a)
            ~(cfn : po_cexpr -> a)
            ~(sfn : po_sexpr -> a)
            ~(custom_ctor : string -> kvlist -> rand_info option -> a)
            ~(get_ctor : Config.origin -> getref -> string -> int -> a)
            ~(coalesce_ctor : po_expr -> po_expr -> a)
            ~(iexpr_ctor : po_cexpr -> po_expr -> a)
            ~(rand_ctor : po_cexpr -> po_cexpr -> po_uexpr -> po_sexpr -> a)
            (e: po_expr) : a = 
  match e with 
  | Null -> t_null
  | Aexpr e -> afn e 
  | Bexpr e -> bfn e 
  | Cexpr e -> cfn e 
  | Sexpr e -> sfn e 
  | CustomExpr (name, kvlist, salt) -> custom_ctor name kvlist salt 
  | Get (o, m, s, i) -> get_ctor o m s i
  | Coalesce (attempt, default) -> coalesce_ctor attempt default
  | Iexpr (base, index) -> iexpr_ctor base index
  | RandomVar (weights, choices, unit, salt) ->
    rand_ctor weights choices unit salt 
  | Phi _ -> assert false

let rec to_number (e: po_expr) : po_aexpr = 
  let custom_ctor name kvlist salt = CustomNumber (name, kvlist, salt) in 
  let get_ctor o m s i = GetNumber (o, m, s, i) in 
  let coalesce_ctor attempt default = 
    CoalesceNumber (to_number attempt, to_number default) in 
  let iexpr_ctor base index = AIexpr (base, index) in 
  let rand_ctor weights choices unit salt = 
    RandomNumber (weights, choices, unit, salt) in 
  to_type NullNumber
          ~afn:Utils.identity
          ~bfn:(fun _ -> raise (type_error ~expected:Number ~found:Boolean e))
          ~cfn:(fun _ -> raise (type_error ~expected:Number ~found:Container e))
          ~sfn:(fun _ -> raise (type_error ~expected:Number ~found:String e))
          ~custom_ctor
          ~get_ctor
          ~coalesce_ctor
          ~iexpr_ctor
          ~rand_ctor 
          e   

let rec to_boolean (e: po_expr) : po_bexpr = 
  let custom_ctor name kvlist salt = CustomBoolean (name, kvlist, salt) in 
  let get_ctor o m s i = GetBoolean (o, m, s, i) in 
  let coalesce_ctor attempt default = 
    CoalesceBoolean (to_boolean attempt, to_boolean default) in 
  let iexpr_ctor base index = BIexpr (base, index) in 
  let rand_ctor weights choices unit salt = 
    RandomBoolean (weights, choices, unit, salt) in 
  to_type NullBoolean
          ~afn:(fun e -> 
            BinBinOp (And, Not (BinNumOp (AEquals, NullNumber, e)),
                           Not (BinNumOp (AEquals, PONumber Oratio.zero, e))))
          ~bfn:Utils.identity
          ~cfn:(fun e ->
            BinBinOp (And, Not (BinCtrOp (CEquals, NullContainer, e)),
                           Not (BinNumOp (AEquals, PONumber Oratio.zero, (Length e)))))
          ~sfn:(fun e ->
            BinBinOp (And, Not (BinStrOp (SEquals, NullString, e)),
                           Not (BinStrOp (SEquals, po_empty_string, e))))
          ~custom_ctor:custom_ctor
          ~get_ctor:get_ctor
          ~coalesce_ctor:coalesce_ctor
          ~iexpr_ctor:iexpr_ctor
          ~rand_ctor 
          e                  

let rec to_container (e : po_expr) : po_cexpr = 
  let custom_ctor name kvlist salt = 
    CustomContainer (name, kvlist, Unknown, salt) in 
  let get_ctor o m s i = GetContainer (o, m, s, i, Unknown) in 
  let coalesce_ctor attempt default = 
    CoalesceContainer (to_container attempt, to_container default) in 
  let iexpr_ctor base index = CIexpr (base, index) in 
  let rand_ctor weights choices unit salt = 
    RandomContainer (weights, choices, unit, salt) in 
  to_type NullContainer 
          ~afn:(fun _ -> raise (type_error ~expected:Container ~found:Number e))
          ~bfn:(fun _ -> 
            raise (type_error ~expected:Container ~found:Boolean e))
          ~cfn:Utils.identity
          ~sfn:(fun _ -> raise (type_error ~expected:Container ~found:String e))
          ~custom_ctor:custom_ctor
          ~get_ctor:get_ctor
          ~coalesce_ctor:coalesce_ctor
          ~iexpr_ctor:iexpr_ctor
          ~rand_ctor 
          e    

let rec to_string (e : po_expr) : po_sexpr = 
  let custom_ctor name kvlist salt = 
    CustomString (name, kvlist, salt) in 
  let get_ctor o m s i = GetString (o, m, s, i) in 
  let coalesce_ctor attempt default = 
    CoalesceString (to_string attempt, to_string default) in 
  let iexpr_ctor base index = SIexpr (base, index) in 
  let rand_ctor weights choices unit salt = 
    RandomString (weights, choices, unit, salt) in 
  to_type NullString
          ~afn:(fun _ -> raise (type_error ~expected:String ~found:Number e))
          ~bfn:(fun _ -> raise (type_error ~expected:String ~found:Boolean e))
          ~cfn:(fun _ -> raise (type_error ~expected:String ~found:Container e))
          ~sfn:Utils.identity
          ~custom_ctor:custom_ctor
          ~get_ctor:get_ctor
          ~coalesce_ctor:coalesce_ctor
          ~iexpr_ctor:iexpr_ctor
          ~rand_ctor
          e    

let from_number    e = Aexpr e
let from_boolean   e = Bexpr e
let from_container e = Cexpr e
let from_string    e = Sexpr e

let eget_ctor o m s i = Get (o, m, s, i)
let aget_ctor o m s i = GetNumber (o, m, s, i)
let bget_ctor o m s i = GetBoolean (o, m, s, i)
let cget_ctor t o m s i = GetContainer (o, m, s, i, t)
let sget_ctor o m s i = GetString (o, m, s, i)

let number_to_ratio = function 
  | PONumber r -> r
  | e -> raise (NotFinal (Aexpr e))

let is_get e = match e with 
  | Get _ 
  | Aexpr (GetNumber _)
  | Bexpr (GetBoolean _)
  | Cexpr (GetContainer _)
  | Sexpr (GetString _) -> true 
  | _ -> false 