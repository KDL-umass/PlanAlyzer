type sexp =
  | SList of sexp list
  | SSymbol of string
  | SString of string
  | SKeyword of string
  | SInt of int
  (* | SRatio of int * int *)
  | SBitVec of int * int
