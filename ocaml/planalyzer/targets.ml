(** Available basetypes/Planalyzer targets. *)
module PlanOut = struct
  module Ast = Po_ast 
  module Basetypes = Po_basetypes 
  module Syntax = Po_syntax

  module POConfig : Config.Config  
    with type basetype = Basetypes.base_type = Config.Make(struct
        type basetype = Basetypes.base_type
        let t_default = Basetypes.Unknown
        let sexp_of_basetype = Basetypes.sexp_of_base_type
        let basetype_of_sexp = Basetypes.base_type_of_sexp 
      end)
  module DDG = Ast.PODdg  
  module Parse = Ast.MakeParse(POConfig) 
  module Normalize : Ast.Normalize 
    with type typequals = POConfig.typequals 
    = Ast.MakeNormalize(POConfig)
  module Tform = Po_transform.Make(struct 
    let smt = "z3"  
    let mock = false 
    let max_choices = Inputs.max_choices
    module POCfg = POConfig
    module PODdg = DDG
    end) 
  module POCorepo = Tform.Corepo
  module StaticErrors = POCorepo.Static_errors  
  module ATE = Ate.MakeAte(struct 
      include POCorepo
      module Ddg = DDG
    end)
  module CGM = Ate.MakeCgm(struct 
      include Tform.Corepo 
      let get_references e = 
        Ast.Aux.get_node_vars (Syntax.Expr e) 
        |> Config.Params.elements
      let get_delta_key (s, _) = s  
      let is_constant = Ast.Aux.is_constant
    end)

  let register_printers () = 
    let open Printf in 
    Printexc.register_printer (function
      | Parse.MissingUnitError (expected, keys) ->
        Some (sprintf "No unit key \"%s\" in keys [%s]" expected
          (Utils.join "; " Utils.identity keys))
      | Parse.Malformed_unit e ->
        Some ("Malformed unit of randomization: " ^ 
          (Ast.Format.ast_string_of_expr e))
      | Parse.Malformed_json s -> Some ("ParseError: " ^ s)
      | Config.UnitError s -> 
        Some (sprintf "Var/function %s marked as random, but missing unit of randomization." s)
      | Normalize.Static_unit_error (name, expr) ->
        Some (sprintf "Unit of randomization for random function \"%s\" not statically decidable: %s" name (Ast.Format.string_of_expr expr))
      | StaticErrors.UnloggedPathRandomization path ->
        Some (sprintf "Unlogged path contains randomized treatment: %s"
        (POCorepo.Format.string_of_path path))
      | StaticErrors.LoggedPathNoRandomization path ->
        Some (sprintf "Logged path contains no randomization: %s"
          (POCorepo.Format.string_of_path path))
      | StaticErrors.UnitLowCardinality unit_str ->
        Some (sprintf "Unit of randomization %s has low cardinality" unit_str)
      | Parse.CodomainMismatch (kwd, should_be, js) -> 
        Some (sprintf "Kwd %s not type %s in %s" 
          (Po_kwd.string_of_kwd kwd)
          (Basetypes.string_of_base_type should_be)
          (Yojson.Basic.to_string js))
      | Parse.PlanOut_syntax (e, t) ->
        Some (sprintf "Expression %s is not type %s"
          (Po_format.ast_string_of_expr e)
          (Po_basetypes.string_of_base_type t)
        )
      | Po_syntax.TypeError (expected, found, expr) ->
        Some (sprintf "Expression %s type error: expected %s but found %s"
          (Po_format.string_of_expr expr)
          (Po_basetypes.string_of_base_type expected)
          (Po_basetypes.string_of_base_type found)
        )
      | _ -> None)
end