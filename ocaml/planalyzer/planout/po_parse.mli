(** This module handles all of the parsing logic to transform input PlanOut 
programs into their internal ASTs. *)

module type Parse = sig

  module POConfig : Config.Config 
    with type basetype = Po_syntax.base_type
  type typequals 
  exception MissingUnitError of string * string list
  exception Malformed_unit of Po_syntax.po_expr
  exception Malformed_json of string 
  exception CodomainMismatch of Po_kwd.kwd * Po_syntax.base_type * Yojson.Basic.json
  exception PlanOut_syntax of Po_syntax.po_expr * Po_syntax.base_type 
  (** PlanOut allowed some limited type coersions. This function raises an 
    error when we try to go in the wrong direction. These are the only 
    permitted coersions:

      number -> boolean 
        - Rewrites the numeric expression as test for whether it is not zero. 
      container -> boolean 
        - Rewrites the container as an expression that checks whether the 
          container is empty. 
      string -> boolean 
        - Tests whether the string is empty. 

      Right now, this check is only run for custom expressions in the Parse 
      module. There are other downstream type checks. 
    *)
  val make_coersion_err : string -> t_from:Po_syntax.base_type -> 
    t_to:Po_syntax.base_type -> exn

  (** Custom random functions must still supply a unit of randomization. See 
      Config.mli for a description of how to supply the name of the unit of 
      randomization argument. If it is missing, planalyzer will throw an error. 
      *)
  val make_missing_unit_err : fn:string -> unit:string -> exn

  (** Executes the PlanOut compiler, located at $PLANOUT on the input string. 
      Note: creates a temp file for the input string. *)
  val exec_po_compiler : string -> string 

  (** Parses the input program. Will implement some minor pre-processing 
      changes to the input program; involution with string_of_program for the 
      original program not guaranteed. Involution should hold for subsequent 
      calls between string_of_program and make_program. *)
  val make_program : typequals -> Yojson.Basic.json -> Po_syntax.program 

end

module MakeParse (
  POCfg : Config.Config with type basetype = Po_syntax.base_type
  ) : Parse
    with type typequals = POCfg.typequals
    and module POConfig = POCfg