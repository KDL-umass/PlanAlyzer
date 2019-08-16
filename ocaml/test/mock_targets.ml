(** Available basetypes/Planalyzer targets. *)

module PlanOut = struct
  module Basetypes = Po_basetypes 
  module POConfig : Config.Config with type basetype = Po_basetypes.base_type = 
    Config.Make(struct
        type basetype = Po_basetypes.base_type
        let t_default = Po_basetypes.Unknown
        let sexp_of_basetype = Po_basetypes.sexp_of_base_type
        let basetype_of_sexp = Po_basetypes.base_type_of_sexp
      end)
  module DDG = Po_ast.PODdg
  module Parse = Po_ast.MakeParse(POConfig) 
  module Normalize : Po_ast.Normalize 
    with type typequals = POConfig.typequals = Po_ast.MakeNormalize (POConfig)
  module Transform = Po_transform.Make(struct
    let smt = "z3"
    let mock = true 
    let max_choices = ref 10
    module POCfg = POConfig
    module PODdg = DDG
    end)
  module POCorepo = Transform.Corepo
  module StaticErrors = POCorepo.Static_errors
  module ATE = Ate.MakeAte(struct include POCorepo module Ddg = DDG end)
  module CGM = Ate.MakeCgm(struct 
      include POCorepo
      let get_references e = Po_ast.Aux.get_node_vars (Po_syntax.Expr e) 
        |> Config.Params.elements
      let get_delta_key (s, _) = s  
      let is_constant = Po_ast.Aux.is_constant
    end)

  let register_printers () = 
    let open Printf in 
    Printexc.register_printer (function
      | Parse.MissingUnitError (expected, keys) ->
        Some (sprintf "No unit key \"%s\" in keys [%s]" expected
          (Utils.join "; " Utils.identity keys))
      | Config.UnitError s -> 
        Some (sprintf "Var/function %s marked as random, but missing unit of randomization." s)
      | Normalize.Static_unit_error (name, expr) ->
        Some (sprintf "Unit of randomization for random function \"%s\" not statically decidable: %s" name (Po_ast.Format.string_of_expr expr))
      | StaticErrors.UnloggedPathRandomization path ->
        Some (sprintf "Unlogged path contains randomized treatment: %s"
        (POCorepo.Format.string_of_path path))
      | StaticErrors.RandomVariableChoiceFailure (salt, num_choices) ->
        Some (sprintf "Random variable having salt \"%s\" has %d choices." 
          salt num_choices)
      | StaticErrors.LoggedPathNoRandomization pi ->
        Some (sprintf "No randomization on path: %s" 
          (POCorepo.Format.string_of_path pi))
      | DDG.GraphError (key, g) -> 
        Some (sprintf "Cound not find key \"%s_%d\" in graph %s."
          (fst key) (snd key) (DDG.string_of_graph g))
      | CGM.GraphError (key, g) ->
        Some (sprintf "Cound not find key \"%s\" in graph %s." 
          key (CGM.string_of_graph g))
      | Po_syntax.TypeError (found, expected, expr) ->
        Some (sprintf "Expected expression %s to have type %s; found type %s.\nAST:%s"
          (Po_format.string_of_expr expr)
          (Po_syntax.show_base_type expected)
          (Po_syntax.show_base_type found)
          (Po_format.ast_string_of_expr expr)
        )
      | _ -> None);    
    
end
