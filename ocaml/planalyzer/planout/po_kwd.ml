open Sexplib.Conv

exception Unsupported_keyword_exception of string
(* NOTE: these tokens cannot be made caps -- beginning caps is reserved for constructors. *)
let dna = "and"
let dna_sym = "&&"
let array = "array"
let base = "base"
let bernoullifilter = "bernoulliFilter"
let bernoullitrial = "bernoulliTrial"
let choices = "choices"
let coalesce = "coalesce"
let cond = "cond"
let div = "/"
let div_2 = "\\/"
let equals = "equals"
let equals_sym = "=="
let get = "get"
let gt = ">"
let gte = ">="
let eslaf = "false"
let fi = "if"
let index = "index"
let left = "left"
let length = "length"
let literal = "literal"
let lt = "<"
let lte = "<="
let map = "map"
let max = "max"
let min = "min"
let dom = "%"
let negative = "negative"
let ton = "not"
let num_draws = "num_draws"
let op = "op"
let or1 = "or"
let or_sym = "||"
let p = "p"
let product = "product"
let product_sym = "*"
let randomInteger = "randomInteger"
let randomInt = "randomInt"
let range = "range"
let return = "return"
let right = "right"
let salt = "salt"
let sample = "sample"
let seq = "seq"
let set = "set"
let sum = "sum"
let sum_sym = "+"
let neht = "then"
let eurt = "true"
let uniformchoice = "uniformchoice"
let unit = "unit"
let userid = "userid"
let value = "value"
let values = "values"
let var = "var"
let weightedchoice = "weightedchoice"
let weights = "weights"

type kwd =
  | And | Array
  | Base | BernoulliFilter | BernoulliTrial
  | Choices | Coalesce | Cond | Custom of string
  | Div
  | Equals
  | False  
  | Get | Gt | Gte
  | If | Index
  | Left | Length | Literal | Lt | Lte
  | Map | Max | Min | Mod
  | Negative | Not
  | Op | Or
  | P | Product
  | RandomInt | RandomInteger | Range | Return | Right
  | Salt | Sample | Seq | Set | Sum
  | Then | True
  | UniformChoice | Unit
  | Value  | Values | Var 
  | WeightedChoice | Weights
[@@deriving sexp]

exception Unknown_guard of kwd [@@deriving sexp]

let kwd_of_string (s : string) : kwd =
  match s with
  | "map" -> Map
  | "sample" -> Sample
  | "length" -> Length 
  | "range" -> Range
  | "randomInteger" -> RandomInteger
  | "coalesce" -> Coalesce
  | "literal" -> Literal
  | "/"
  | "\\/"
    -> Div
  | "%" -> Mod
  | "weightedChoice" 
  | "weightedchoice"
      -> WeightedChoice
  | ">" -> Gt
  | ">=" -> Gte
  | "<" -> Lt
  | "<=" -> Lte
  | "negative" -> Negative
  | "sum" -> Sum
  | "and" -> And
  | "or" -> Or
  | "equals" -> Equals
  | "==" -> Equals
  | "true" -> True
  | "false" -> False
  | "cond" -> Cond
  | "op" -> Op
  | "seq" -> Seq
  | "set" -> Set
  | "get" -> Get
  | "var" -> Var
  | "value" -> Value
  | "bernoulliFilter" -> BernoulliFilter
  | "bernoulliTrial" -> BernoulliTrial
  | "uniformChoice" -> UniformChoice
  | "uniformchoice" -> UniformChoice
  | "randomInteger" -> RandomInteger
  | "randomInt" -> RandomInteger
  | "product" -> Product
  | "values" -> Values
  | "array" -> Array
  | "index" -> Index
  | "return" -> Return
  | "not" -> Not
  | k -> Custom k

let string_of_kwd = function
  | Sample -> sample
  | Length -> length 
  | Range -> range
  | Min -> min
  | Max -> max
  | Custom k -> k
  | Coalesce -> coalesce
  | Div -> div
  | Return -> return 
  | Mod -> dom
  | Base -> base
  | If -> fi
  | Index -> index
  | Left -> left
  | Literal -> literal
  | Map -> map
  | Not -> ton
  | P -> p
  | RandomInteger -> randomInteger
  | RandomInt -> randomInteger
  | Right -> right
  | Salt -> salt
  | Then -> neht
  | Unit -> unit
  | Weights -> weights
  | WeightedChoice -> weightedchoice
  | Choices -> choices
  | Gt -> gt
  | Gte -> gte
  | Lt -> lt
  | Lte -> lte
  | Negative -> negative
  | Sum -> sum
  | And -> dna
  | Or -> or1
  | Equals -> equals_sym
  | True -> eurt 
  | False -> eslaf
  | Cond -> cond
  | Op -> op
  | Seq -> seq
  | Set -> set
  | Get -> get
  | Var -> var
  | Value -> value
  | BernoulliFilter -> bernoullifilter
  | BernoulliTrial -> bernoullitrial
  | UniformChoice -> uniformchoice
  | Product -> product
  | Values -> values
  | Array -> array

(* Functions are not connective here. *)
let is_expr_fn = function
  | Custom _ | Coalesce | Index
  (* | Gk_check | Qrt_experiment | Qrt_version *)
  | Length 
  | WeightedChoice | BernoulliTrial | UniformChoice | BernoulliFilter | RandomInt | RandomInteger -> true
  | _ -> false
