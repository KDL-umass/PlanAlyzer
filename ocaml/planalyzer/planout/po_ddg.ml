(** Dependencies:
    - Po_aux
    - po_env
    - Po_syntax
*)
module PODdg : Ddg.Ddg 
  with type program = Po_syntax.program
  and type key = Config.ssa_id = Ddg.Make(struct 
    include Po_syntax
    open Printf
    type key = Po_env.env_key  
    let key_compare (p1 : key) (p2 : key) =
        let name_compare = compare (fst p1) (fst p2) in
        if name_compare <> 0
        then name_compare
        else compare (snd p1) (snd p2)
    let key_to_str (s, i) = sprintf "%s_%d" s i 
    let get_program_variables p = 
      Po_aux.get_program_vars p
      |> Config.Params.elements 
    let find_dependents program var = 
       (* Find where var is assigned and then compute dependents from that    
          program segment. *)
      let (Program p) = program in 
      let (s, i) = var in 
      let find_fn (n : ast_node) = match n with 
        | Assignment (_, s', i', _) -> s = s' && i = i'
        | _ -> false in 
      let segment = Po_aux.get_ast_subtree ~find_fn:find_fn p in 
      let rec helper n = 
        let get_assignments = Po_aux.get_node_vars ~efn:(fun _ -> false) 
                                                ~afn:(fun _ -> false)
                                                ~bfn:(fun _ -> false)
                                                ~cfn:(fun _ -> false)
                                                ~sfn:(fun _ -> false) in
        match n with 
        | Assignment (_, t, j, e) -> 
          (* Explicit flows: any time a variable appears on the RHS of 
             an assignment, then the LHS is a dependent.
           *)
          let deps = Po_aux.get_node_vars (Expr e) in 
          if Config.Params.mem var deps 
          then [(t, j)]
          else []
        | Cond ((g, conds)::t) -> 
          (* Implicit flows: if a variable appears in a guard, then all of the 
          variables defined in every subsequent conditional block are 
          dependents. *)
          let uses = Po_aux.get_node_vars g in 
          if Config.Params.mem var uses
          then conds::(List.map snd t)
               |> List.fold_left (fun p c -> 
                    let dependent_assignments = get_assignments c in 
                    Config.Params.union p dependent_assignments) 
                  Config.Params.empty
               |> Config.Params.elements
          else helper conds @ (helper (Cond t))
        | Seq (h::t) ->
          let deps = helper h in 
          if List.length deps = 0 
          (* If I have no dependencies in h, move on. *)
          then helper (Seq t)
          else 
          (* O/W, check to see if the return depends on var. If so, then all 
          subsequent assignments depend on var. *)
            let has_return = Po_aux.get_ast_subtree 
              ~find_fn:(fun n -> match n with Return _ -> true | _ -> false) 
              h <> None in 
            if has_return 
            then 
              let guard_vars = Po_aux.get_guard_vars (Program h) in 
              if Config.Params.mem var guard_vars 
              then 
                let deps2 = get_assignments (Seq t) in 
                Config.Params.of_list deps
                |> Config.Params.union deps2
                |> Config.Params.elements
              else deps
            else deps @ (helper (Seq t))
        | _ -> []
      in 
      match segment with 
      | Some n -> helper n
      | None -> 
        (* Then the var is external? *)
        helper p
  end) 
