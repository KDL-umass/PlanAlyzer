open OUnit2
open Programs_aux
open Config 

open Mock_targets.PlanOut
module CPO = POCorepo
module PO = Po_syntax
module BT = Po_basetypes

let make_program = make_program2 Parse.exec_po_compiler Parse.make_program
let cfg = POConfig.load_annotations_json default_annot
let default_quals = {CPO.card=Low; CPO.dyn=Const; CPO.rand=Det; CPO.corr=Exo}
let default_decl = {CPO.card=Low; CPO.dyn=Const; CPO.rand=Det; CPO.corr=End}
let make_quals ?(card=Low) ?(dyn=Const) ?(rand=Det) ?(corr=Exo) _ = 
    CPO.make_qualifiers ~card ~dyn ~rand ~corr

let one_half = PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1,2)))
let bernoulli_choices = PO.POArray (PO.Boolean, [
        PO.Bexpr (PO.POBoolean false); 
        PO.Bexpr (PO.POBoolean true)
    ])


let print_cpoprog p =
    CPO.Format.string_of_program p
    |> Printf.printf "%s\n"

let print_cpo_ast p = 
    Printf.printf "\n%s\n" (POCorepo.Format.ast_string_of_program p)

let rec ast_equal (is : CPO.program) (should_be : CPO.program) = 
  let open Printf in 
  let rec path_equal path_num (is : CPO.pi) (should_be : CPO.pi) = 
    let path_equal = path_equal path_num in 
    match is, should_be with 
    | (CPO.Assert a as n1)::p1, (CPO.Assert b as n2)::p2 -> 
      assert_bool (sprintf "Assertions not equal:\n\t%s\nvs.\n\t%s"
        (CPO.Format.string_of_node n1) 
        (CPO.Format.string_of_node n2)) 
        (a = b);
      path_equal p1 p2 
    | CPO.Assign (o1, k1, q1, e1)::p1, CPO.Assign (o2, k2, q2, e2)::p2 ->
      let s1 = CPO.Format.string_of_id k1 in 
      let s2 = CPO.Format.string_of_id k2 in 
      assert_bool (sprintf 
        "Path %d: Assignment names not equal: %s vs %s" path_num s1 s2)
        (k1 = k2);
      assert_bool (sprintf 
        "Path %d: Origins for assignments %s and %s not equal: %s vs. %s"
        path_num s1 s2 
        (Po_env.string_of_origin o1) (Po_env.string_of_origin o2))
        (o1 = o2);
      assert_bool (sprintf 
        "Path %d: Labels for assignments to %s not equal: %s vs. %s"
        path_num s1 
        (CPO.Format.string_of_qualifier q1) (CPO.Format.string_of_qualifier q2))
        (q1 = q2);
      assert_bool (sprintf 
        "Path %d: Expressions for %s and %s not equal:\n\t%s\nvs.\n\t%s\n\n%s\n\tvs.\n%s"
        path_num s1 s2 
        (CPO.Format.string_of_inlang_expr e1) 
        (CPO.Format.string_of_inlang_expr e2)
        (Ast.Format.ast_string_of_expr e1) (Ast.Format.ast_string_of_expr e2))
        (e1 = e2);
      path_equal p1 p2
    | (CPO.Declare (k1, q1, t1) as n1)::p1, 
      (CPO.Declare (k2, q2, t2) as n2)::p2 ->
      assert_bool (sprintf 
        "Path %d: Declarations not equal:\n\t%s vs.\n\t%s" 
        path_num 
        (CPO.Format.string_of_node n1) (CPO.Format.string_of_node n2))
        (n1 = n2);
      path_equal p1 p2
    | (CPO.Return a as n1)::p1, (CPO.Return b as n2)::p2 -> assert_bool (sprintf 
        "Path %d: Logging not equal: %s vs. %s" 
        path_num 
        (CPO.Format.string_of_node n1) (CPO.Format.string_of_node n2))
        (a = b);
      path_equal p1 p2
    | n1::p1, n2::p2 -> assert_bool (sprintf 
      "Path %d: Nodes not aligned:\n\t%s vs.\n\t%s"
        path_num 
        (CPO.Format.string_of_node n1)
        (CPO.Format.string_of_node n2))
        (n1 = n2);
      path_equal p1 p2
    | [], [] -> ()
    | [], _  -> assert_bool (sprintf "Path %d: Missing rest of path: %s" 
        path_num 
        (CPO.Format.string_of_path should_be))
        false
    | _, [] -> assert_bool (sprintf 
      "Path %d: Returned path is longer than expected: %s"
        path_num
        (CPO.Format.string_of_path is))
        false in 
  let rec helper ?(path_num=0) is should_be = match is, should_be with 
    | [], [] -> ()
    | p1::t1, p2::t2 -> 
        path_equal path_num p1 p2; 
        helper ~path_num:(path_num + 1) t1 t2
    | p::t, [] -> 
      assert_bool (sprintf "Found extra path(s) at index %d: %s"
        path_num 
        (CPO.Format.string_of_program is))
        false
    | [], p::t ->
      assert_bool (sprintf "Missing expected path(s) at index %d: %s"
       path_num 
       (CPO.Format.string_of_program should_be))
       false in 
  helper is should_be 
      
 
let transform_program cfg p =
  let (cfg, prog) = make_program cfg p 
                    |> Normalize.normalize cfg in 
  Transform.transform (Ast.PODdg.build_dependence_graph prog) cfg prog

let test_tranform_straight_line ctxt = 
    let is = transform_program cfg p1 in 
    let open Config in 
    let should_be = [[
        CPO.Assign (Source, ("foo", 1), default_quals, 
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 10)));
        CPO.Assign (Source, ("bar", 1), default_quals,
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 90)));
        CPO.Assign (Source, ("baz", 1), default_quals,
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 30)));
        CPO.Return CPO.False
    ]] in 
    (*print_CorePOprog is;
    print_CorePOprog should_be;*)
    ast_equal is should_be

let test_transform_straight_line_with_rv ctxt = 
    let open Config in 
    let is = transform_program cfg p2 in 
    let w1 = PO.PONumber (Oratio.ReducedRatio (10, 1)) in 
    let w2 = PO.PONumber (Oratio.ReducedRatio (2, 5)) in 
    let w1' = PO.PONumber (Oratio.ReducedRatio (25, 26)) in 
    let w2' = PO.PONumber (Oratio.ReducedRatio (1, 26)) in 
    let c1 = PO.POString "asdf" in 
    let c2 = PO.POBoolean true in 
    let should_be = [[ 
        CPO.Assign (Source, ("weights", 1), default_quals,
            PO.Cexpr (PO.POArray 
                (BT.Number, [PO.Aexpr w1; PO.Aexpr w2])));
        CPO.Assign (Source, ("choices", 1), default_quals,
            PO.Cexpr (PO.POArray 
                (BT.Unknown, [PO.Sexpr c1; PO.Bexpr c2])));
        CPO.Assign (Source, ("foo", 1), 
            {CPO.card=Low;
             CPO.dyn=Const; 
             CPO.rand=Rand ["userid"];
             CPO.corr=Exo},
            PO.RandomVar (
                PO.POArray (BT.Number, [PO.Aexpr w1'; PO.Aexpr w2']), 
                PO.POArray (BT.Unknown, [PO.Sexpr c1; PO.Bexpr c2]),
            PO.Userid, 
            PO.POString "foo"));
        CPO.Return CPO.True
    ]] in 
    (*print_CorePOprog is;
    print_CorePOprog should_be;*)
    ast_equal is should_be

let test_basic_paths ctxt = 
    let open Config in 
    let is = transform_program cfg p3 in 
    let should_be = [[
        CPO.Declare (("asdf", 0), default_decl, Some Smtlib.bool_sort);
        CPO.Assign (Source, ("foo", 1), default_quals,
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 10)));
        CPO.Assert (CPO.Id ("asdf", 0));
        CPO.Assign (Source, ("foo", 2), default_decl,
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 200)));
        CPO.Assign (Synth, ("foo", 3), default_decl, 
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 200)));
        CPO.Assign (Source, ("bar", 1), default_decl,
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 40000)));
        CPO.Return CPO.True
      ]; [
        CPO.Declare (("asdf", 0), default_decl, Some Smtlib.bool_sort);
        CPO.Assign (Source, ("foo", 1), default_quals,
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 10)));
        CPO.Assert (CPO.Not (CPO.Id ("asdf", 0)));
        CPO.Assign (Synth, ("foo", 3), default_decl, 
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 10)));
        CPO.Assign (Source, ("bar", 1), default_decl,
            PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 100)));
        CPO.Return CPO.True
      ];
    ] in
    assert_equal (List.length is) (List.length should_be);
    (*print_cpoprog is;
    print_cpoprog should_be;
    print_cpo_ast is;
    print_cpo_ast should_be;*)
    ast_equal is should_be

let test_basic_paths_2 ctxt = 
    assert_raises StaticErrors.GuardAlwaysTrue 
        (fun () -> (transform_program cfg p4))

let test_with_fvs_1 ctxt = 
    let open Config in 
    let open Po_basetypes in 
    let is = transform_program cfg p5 in 
    let should_be = [[
      CPO.Declare (("a", 0), default_decl, None);
      CPO.Declare (("b", 0), default_decl, None);
      CPO.Assign (Synth, (prefix ^ "1", 1), default_decl, 
        PO.Iexpr (PO.GetContainer (ExtSource, PO.External, "a", 0, Unknown),
                  PO.Get (ExtSource, PO.External, "b", 0)));
      CPO.Assign (Source, ("foo", 1), default_decl, 
          PO.CustomExpr ("fn", ["arg1", 
                PO.Get (Synth, PO.Delay, prefix ^ "1", 1)], None));
      CPO.Return CPO.True
    ]] in 
    (*print_cpo_ast is;*)
    ast_equal is should_be

let test_with_annotations ctxt = 
  let open PO in 
  let cfg = POConfig.load_annotations_json 
    "{fn : {randomness : \"rand\", unit: \"arg1\"}}" in
  let unitr = (Iexpr (GetContainer (ExtSource, External, "a", 0, Unknown), 
                      Get (ExtSource, External, "b", 0))) in 
  assert_raises 
    (Parse.Malformed_unit unitr)
    (fun () -> transform_program cfg p5)

let test_with_fvs_2 ctxt = 
    let open Config in 
    let is = transform_program cfg p6 in 
    let open Po_basetypes in 
    let should_be = [[
        CPO.Declare (("a", 0), default_decl, None);
        CPO.Declare (("b", 0), default_decl, None);
        CPO.Declare (("fooid", 0), default_decl, None);
        CPO.Assign (Synth, (prefix ^ "1", 1), default_decl, 
            PO.Iexpr (PO.GetContainer (ExtSource, PO.External, "a", 0, 
                        Unknown),
                      PO.Get (ExtSource, PO.External, "b", 0)
            ));
        CPO.Assign (Synth, (prefix ^ "2", 1), 
          make_quals ~corr:End (),
          PO.Aexpr (PO.CustomNumber ("fn", [
                "arg1", PO.Get (Synth, PO.Delay, prefix ^ "1", 1);
                "arg2", PO.Get (ExtSource, PO.External, "fooid", 0)
            ], None)));
        CPO.Assign (Source, ("foo", 1), default_decl, 
            PO.Aexpr (PO.Abinop (PO.Sum, 
                PO.PONumber (Oratio.ratio_of_int 10),
                PO.GetNumber (Synth, PO.Delay, prefix ^ "2", 1)))
        );
        CPO.Return CPO.True
    ]] in 
    (*print_cpoprog is;
    print_cpoprog should_be;
    print_cpo_ast is;
    print_cpo_ast should_be;*)
    ast_equal is should_be

let test_with_fvs_3 ctxt = 
    let open Config in 
    let open Po_basetypes in 
    let is = transform_program cfg p7 in 
    let label_a_length = prefix ^ "1" in 
    let label_b_mod_a_length = prefix ^ "2" in 
    let label_1st_lookup = prefix ^ "3" in 
    let label_2nd_lookup = prefix ^ "4" in 
    let a_length = PO.Aexpr (PO.Length (
        PO.GetContainer (ExtSource, PO.External, "a", 0, Container))) in 
    let b_mod_length_a = PO.Aexpr (PO.Abinop (PO.Mod, 
        PO.GetNumber (ExtSource, PO.External, "b", 0),
        PO.GetNumber (Synth, PO.Delay, label_a_length, 1))) in 
    let first_lookup = PO.Cexpr (PO.CIexpr (
        PO.GetContainer (ExtSource, PO.External, "a", 0, Container),
        PO.Aexpr (PO.GetNumber (Synth, PO.Delay, label_b_mod_a_length, 1)))) in 
    let second_lookup = PO.Cexpr (PO.CIexpr (
        PO.GetContainer (Synth, PO.Delay, label_1st_lookup, 1, Container),
        PO.Get (ExtSource, PO.External, "c", 0))) in 
    let third_lookup = PO.Iexpr (
        PO.GetContainer (Synth, PO.Delay, label_2nd_lookup, 1, Unknown),
        PO.Get (ExtSource, PO.External, "d", 0)) in 
    let should_be = [[
        CPO.Declare (("a", 0), default_decl, None);
        CPO.Declare (("b", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("c", 0), default_decl, None);
        CPO.Declare (("d", 0), default_decl, None);
        CPO.Assign (Synth, (label_a_length, 1), default_decl, a_length);
        CPO.Assign (Synth, (label_b_mod_a_length, 1), default_decl, b_mod_length_a);
        CPO.Assign (Synth, (label_1st_lookup, 1), default_decl, first_lookup);
        CPO.Assign (Synth, (label_2nd_lookup, 1), default_decl, second_lookup);
        CPO.Assign (Source, ("foo", 1), default_decl, third_lookup);
        CPO.Return CPO.True
    ]] in 
    (*print_cpoprog is;
    print_cpoprog should_be;
    print_cpo_ast is;
    print_cpo_ast should_be;*)
    ast_equal is should_be

let test_paths_truncate ctxt = 
    let open Config in 
    let is = transform_program cfg p8 in 
    let label_a_b_eq = prefix ^ "2" in 
    let label_guard = prefix ^ "1" in 

    let assign_a_b_eq = CPO.Assign (Synth, (label_a_b_eq, 1), 
      default_decl, 
      PO.Bexpr (PO.Equals 
          (PO.Get (ExtSource, PO.External, "a", 0),
           PO.Get (ExtSource, PO.External, "b", 0)))) in 
    
    let label_asdf = "asdf" in 
    let get_asdf = PO.GetBoolean (ExtSource, PO.External, label_asdf, 0) in 
    let get_a_b_eq = PO.GetBoolean (Synth, PO.Delay, label_a_b_eq, 1) in 

    let assign_guard =  CPO.Assign (Synth, (label_guard, 1), default_decl, 
      PO.Bexpr (PO.BinBinOp (PO.And, get_asdf, get_a_b_eq))) in 
    
    let should_be = [[
        CPO.Declare (("a", 0), default_decl, None);
        CPO.Declare (("asdf", 0), default_decl, Some Smtlib.bool_sort);
        CPO.Declare (("b", 0), default_decl, None);
        assign_a_b_eq; assign_guard;
        CPO.Assert (CPO.Id (label_guard, 1));   
        CPO.Return CPO.False
      ]; [
        CPO.Declare (("a", 0), default_decl, None);
        CPO.Declare (("asdf", 0), default_decl, Some Smtlib.bool_sort);
        CPO.Declare (("b", 0), default_decl, None);
        assign_a_b_eq; assign_guard;
        CPO.Assert (CPO.Not (CPO.Id (label_guard, 1)));
        CPO.Return CPO.True        
      ]] in 
    (* print_cpoprog is;
    print_cpoprog should_be; *)
    ast_equal is should_be

let test_nested_paths ctxt = 
    let open Config in 
    let open Po_basetypes in 
    let fv1s = prefix ^ "4" in 
    let fv2s = prefix ^ "5" in 
    let fv3s = prefix ^ "6" in 
    let fv4s = prefix ^ "1" in 
    let fv5s = prefix ^ "2" in 

    let assign_fn_arg1_42 = CPO.Assign (Synth, (fv5s, 1),
      default_decl, 
      PO.Bexpr (PO.CustomBoolean ("fn", 
          ["arg1", PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 42))], 
        None))) in 
    
    let label_guard = prefix ^ "3" in
    let get_a_is_zero = PO.GetBoolean (Synth, PO.Delay, fv2s, 1) in 
    let get_b_is_zero = PO.GetBoolean (Synth, PO.Delay, fv1s, 1) in 

    let assign_guard = CPO.Assign (Synth, (label_guard, 1), default_decl, 
        PO.Bexpr (PO.BinBinOp (PO.And, get_a_is_zero, get_b_is_zero))
      ) in 

    let should_be = [
      [
        CPO.Declare (("a", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("b", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("c", 0), default_decl, None);
        CPO.Assign (Synth, (fv1s, 1), default_decl, 
            PO.Bexpr (PO.BinNumOp (PO.AEquals,
                PO.PONumber Oratio.zero, 
                PO.GetNumber (ExtSource, PO.External, "b", 0))));
        CPO.Assign (Synth, (fv2s, 1), default_decl, 
            PO.Bexpr (PO.BinNumOp (PO.AEquals,
                PO.PONumber Oratio.zero, 
                PO.GetNumber (ExtSource, PO.External, "a", 0))));
        assign_guard;
        CPO.Assert (CPO.Id (label_guard, 1));
        CPO.Assign (Synth, (fv3s, 1), default_decl,
            PO.Aexpr (PO.Length (
                PO.GetContainer (ExtSource, PO.External, "c", 0, Unknown))));
        CPO.Assign (Synth, (fv4s, 1), default_decl,
            PO.Bexpr (PO.BinNumOp (PO.Gt, 
                PO.GetNumber (Synth, PO.Delay, fv3s, 1),
                PO.PONumber Oratio.one)));
        assign_fn_arg1_42;
        CPO.Assert (CPO.Id (fv4s, 1));
        CPO.Return CPO.True;
      ]; [
        CPO.Declare (("a", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("b", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("c", 0), default_decl, None);
        CPO.Assign (Synth, (fv1s, 1), default_decl, 
            PO.Bexpr (PO.BinNumOp (PO.AEquals,
                PO.PONumber Oratio.zero, 
                PO.GetNumber (ExtSource, PO.External, "b", 0))));
        CPO.Assign (Synth, (fv2s, 1), default_decl, 
            PO.Bexpr (PO.BinNumOp (PO.AEquals,
                PO.PONumber Oratio.zero, 
                PO.GetNumber (ExtSource, PO.External, "a", 0))));
        assign_guard;
        CPO.Assert (CPO.Id (label_guard, 1));
        CPO.Assign (Synth, (fv3s, 1), default_decl,
            PO.Aexpr (PO.Length (
                PO.GetContainer (ExtSource, PO.External, "c", 0, Unknown))));
        CPO.Assign (Synth, (fv4s, 1), default_decl,
            PO.Bexpr (PO.BinNumOp (PO.Gt, 
                PO.GetNumber (Synth, PO.Delay, fv3s, 1),
                PO.PONumber Oratio.one)));
        assign_fn_arg1_42;
        CPO.Assert (CPO.And (CPO.Id (fv5s, 1), CPO.Not (CPO.Id (fv4s, 1))));
        CPO.Return CPO.False
      ]; [
        CPO.Declare (("a", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("b", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("c", 0), default_decl, None);
        CPO.Assign (Synth, (fv1s, 1), default_decl, 
            PO.Bexpr (PO.BinNumOp (PO.AEquals,
                PO.PONumber Oratio.zero, 
                PO.GetNumber (ExtSource, PO.External, "b", 0))));
        CPO.Assign (Synth, (fv2s, 1), default_decl, 
            PO.Bexpr (PO.BinNumOp (PO.AEquals,
                PO.PONumber Oratio.zero, 
                PO.GetNumber (ExtSource, PO.External, "a", 0))));
        assign_guard;
        CPO.Assert (CPO.Id (label_guard, 1));
        CPO.Assign (Synth, (fv3s, 1), default_decl,
            PO.Aexpr (PO.Length (
                PO.GetContainer (ExtSource, PO.External, "c", 0, Unknown))));
        CPO.Assign (Synth, (fv4s, 1), default_decl,
            PO.Bexpr (PO.BinNumOp (PO.Gt, 
                PO.GetNumber (Synth, PO.Delay, fv3s, 1),
                PO.PONumber Oratio.one)));
        assign_fn_arg1_42;
        CPO.Assert (CPO.Not (CPO.Or (CPO.Id (fv5s, 1), CPO.Id (fv4s, 1))));
        CPO.Return CPO.True  
      ]; [
        CPO.Declare (("a", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("b", 0), default_decl, Some Smtlib.int_sort);
        CPO.Declare (("c", 0), default_decl, None);
        CPO.Assign (Synth, (fv1s, 1), default_decl, 
            PO.Bexpr (PO.BinNumOp (PO.AEquals,
                PO.PONumber Oratio.zero, 
                PO.GetNumber (ExtSource, PO.External, "b", 0))));
        CPO.Assign (Synth, (fv2s, 1), default_decl, 
            PO.Bexpr (PO.BinNumOp (PO.AEquals,
                PO.PONumber Oratio.zero, 
                PO.GetNumber (ExtSource, PO.External, "a", 0))));
        assign_guard;
        CPO.Assert (CPO.Not (CPO.Id (label_guard, 1)));
        CPO.Return CPO.True
      ]] in 
    (* print_cpoprog is; *)
    (* print_cpoprog should_be; *)
    (* assert_equal 
      (StaticErrors.CausalSufficiencyError "") *)
    let is = transform_program cfg p9 in
    (*let p1_is = List.hd is in 
    let p1_should_be = List.hd should_be in 
    (*print_cpo_ast [List.hd is];
    print_cpo_ast should_be;*)
    assert_equal p1_is p1_should_be;
    let p2_is = List.nth is 1 in 
    let p2_should_be = List.nth should_be 1 in 
    (*print_cpo_ast [List.nth is 1];
    print_cpo_ast [List.nth should_be 1];*)
    assert_equal p2_is p2_should_be; *)
    ast_equal is should_be

let test_nested_rvs ctxt = 
    let open Config in 
    let open Po_basetypes in 
    let is = transform_program cfg p10 in 
    let weights = PO.POArray (Container, [
                PO.Cexpr (PO.POArray (Number, [
                    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 10)));
                    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 5)))
                ]));
                PO.Cexpr (PO.POArray (Number, [
                    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (3, 10)));
                    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (2, 5)))
                ]))
            ]) in 
    let choices = PO.POArray (Container, [
                PO.Cexpr (PO.POArray (Number, [
                    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (4, 1)));
                    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (3, 1)))]));
                PO.Cexpr (PO.POArray (Number, [
                    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (2, 1)));
                    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 1)))
                ]))
            ]) in 
    let get_bar = PO.GetBoolean (Synth, PO.Random, "bar", 1) in 
    let get_baz = PO.GetBoolean (Synth, PO.Random, "baz", 1) in 
    let should_be = [[
        CPO.Assign (Source, ("weights", 1), default_quals, PO.Cexpr weights);
        CPO.Assign (Source, ("choices", 1), default_quals, PO.Cexpr choices);
        CPO.Assign (Synth, ("bar", 1), 
          make_quals ~rand:(Rand ["userid"]) (), 
          PO.Bexpr (PO.RandomBoolean (
            PO.POArray (Number, [
                PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 2)));
                PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 2)))
            ]),
            PO.POArray (Boolean, [
                PO.Bexpr (PO.POBoolean false); PO.Bexpr (PO.POBoolean true)
            ]),
            PO.Userid, PO.POString "bar"
          )));
        CPO.Assign (Synth, ("baz", 1), 
          make_quals ~rand:(Rand ["userid"]) (), 
          PO.Bexpr (PO.RandomBoolean (
            PO.POArray (Number, [
                PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (2, 5)));
                PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (3, 5)))
            ]),
            PO.POArray (Boolean, [
                PO.Bexpr (PO.POBoolean false); PO.Bexpr (PO.POBoolean true)
            ]),
            PO.Userid, PO.POString "baz"
          )));
        CPO.Assign (Source, ("foo", 1), 
          make_quals ~rand:(Rand ["userid"]) (),
          PO.Aexpr (PO.RandomNumber (
            PO.CIexpr (weights, PO.Bexpr get_bar),
            PO.CIexpr (choices, PO.Bexpr get_baz),
            PO.Userid, PO.POString "foo"
          )));
        CPO.Return CPO.True
    ]] in 
    (*print_cpoprog is;
    print_cpoprog should_be;
    print_cpo_ast is;
    print_cpo_ast should_be;*)
    ast_equal is should_be

let test_transform_p12 ctxt = 
    (* In test_semantics, p12 had an expression that erroneously labeled abc as 
    Delay. This only happened in one of the expressions abc appeared in. Added 
    this test when tracking down where in the process the 
    erroneous label was assigned. *)
    let cfg = POConfig.load_annotations_json 
        "{extRandFn : {randomness: \"rand\", unit : \"unit\"}}" in 
    let open Config in 
    let is = transform_program cfg p12 in 
    let open Syntax in 
    let rand_quals = make_quals ~rand:(Rand ["someid"]) () in 
    let (rand_info : rand_info) = {
        salt = POString "abc";
        unit_arg = "unit";
        unit_value = Id "some"
      } in 
    let assign_abc = CPO.Assign (Source, ("abc", 1), rand_quals,
      Aexpr (CustomNumber ("extRandFn", [], Some rand_info))) in 
    let assign_abc_is_1234 = CPO.Assign (Synth, (prefix ^ "1", 1), 
      rand_quals, 
      Bexpr (BinNumOp (AEquals, 
        PONumber (Oratio.ReducedRatio (1234, 1)), 
        GetNumber (Source, Random, "abc", 1)))) in
    let assign_abc_is_2345 = CPO.Assign (Synth, (prefix ^ "2", 1), 
      rand_quals, 
      Bexpr (BinNumOp (AEquals, 
        PONumber (Oratio.ReducedRatio (2345, 1)), 
        GetNumber (Source, Random, "abc", 1)))) in 
    let assign_abc_is_3456 = CPO.Assign (Synth, (prefix ^ "3", 1), 
      rand_quals,
      Bexpr (BinNumOp (AEquals,
        PONumber (Oratio.ReducedRatio (3456, 1)),
        GetNumber (Source, Random, "abc", 1)))) in 
    let assign_abc_lt_5000 = CPO.Assign (Synth, (prefix ^ "4", 1), 
        rand_quals, 
        Bexpr (BinNumOp (Lt, 
          GetNumber (Source, Random, "abc", 1), 
          PONumber (Oratio.ReducedRatio (5000, 1))))) in 
    let should_be = [
      [
        assign_abc; 
        assign_abc_is_1234; assign_abc_is_2345; assign_abc_is_3456;
        assign_abc_lt_5000;
        CPO.Assert (CPO.Id (prefix ^ "1", 1));
        CPO.Assign (Source, ("foo", 1), rand_quals, Sexpr(POString "a"));
        CPO.Assign (Synth, ("foo", 6), rand_quals, Sexpr(POString "a"));
        CPO.Return CPO.True];
      [ 
        assign_abc; 
        assign_abc_is_1234; assign_abc_is_2345; assign_abc_is_3456;
        assign_abc_lt_5000;
        CPO.Assert (CPO.And (
            CPO.Id (prefix ^ "2", 1), 
            CPO.Not (CPO.Id (prefix ^ "1", 1))));
        CPO.Assign (Source, ("foo", 2), rand_quals, Sexpr (POString "b"));
        CPO.Assign (Synth, ("foo", 6), rand_quals, Sexpr(POString "b"));
        CPO.Return CPO.True];
      [
        assign_abc; 
        assign_abc_is_1234; assign_abc_is_2345; assign_abc_is_3456;
        assign_abc_lt_5000;
        CPO.Assert (CPO.And (
            CPO.Id (prefix ^ "3", 1), 
            CPO.Not (CPO.Or (
                CPO.Id (prefix ^ "2", 1), 
                (CPO.Id (prefix ^ "1", 1))))));
        CPO.Assign (Source, ("foo",  3), rand_quals, Sexpr (POString "c"));
        CPO.Assign (Synth, ("foo", 6), rand_quals, Sexpr (POString "c"));
        CPO.Return CPO.True];
      [
        assign_abc; 
        assign_abc_is_1234; assign_abc_is_2345; assign_abc_is_3456;
        assign_abc_lt_5000;
        CPO.Assert (CPO.And 
          (CPO.Id (prefix ^ "4", 1), 
           CPO.Not (CPO.Or 
             (CPO.Id (prefix ^ "3", 1), 
              CPO.Or (CPO.Id (prefix ^ "2", 1), CPO.Id (prefix ^ "1", 1))))));
        CPO.Assign (Source, ("foo", 4), rand_quals, 
            Sexpr (POString "d"));
        CPO.Assign (Synth, ("foo", 6), rand_quals, 
            Sexpr (POString "d"));
        CPO.Return CPO.True];
      [
        assign_abc; 
        assign_abc_is_1234; assign_abc_is_2345; assign_abc_is_3456;
        assign_abc_lt_5000;
        CPO.Assert (CPO.Not (CPO.Or
          (CPO.Id (prefix ^ "4", 1), 
           CPO.Or 
             (CPO.Id (prefix ^ "3", 1), 
              CPO.Or
                (CPO.Id (prefix ^ "2", 1),
                 CPO.Id (prefix ^ "1", 1))))));
        CPO.Assign (Source, ("foo", 5), rand_quals, Sexpr (POString "e"));
        CPO.Assign (Synth, ("foo", 6), rand_quals, Sexpr (POString "e"));
        CPO.Return CPO.True]] in 
    (*print_POCorepoprog is;*)
    (*print_cpo_ast should_be;*)
    ast_equal is should_be

let test_transform_p6 ctxt = 
  let cfg = POConfig.load_annotations_json "{fn : {randomness : \"rand\", 
    codomain : \"number\", \"unit\" : \"arg2\"}, fooid : {card : \"high\"} }" in
  let open Po_syntax in 
  let is = transform_program cfg p6 in 
  let a = PO.GetContainer (Config.ExtSource, PO.External, "a", 0, Unknown) in 
  let b = PO.Get (ExtSource, PO.External, "b", 0) in 
  let indexing_label = prefix ^ "2" in 
  let fn_call_label = prefix ^ "1" in 
  let fv1 = PO.Get (Synth, PO.Delay, indexing_label, 1) in 
  let fv2 = PO.GetNumber (Synth, PO.Random, fn_call_label, 1) in
  let (rand_info : rand_info) = {
      salt = POString "";
      unit_arg = "arg2";
      unit_value = Id "foo"
  } in 
  let rand_quals = make_quals ~rand:(Rand ["fooid"]) () in 
  let end_quals = make_quals ~corr:End () in 
  let should_be = [
    [
        CPO.Declare (("a", 0), default_decl, None);
        CPO.Declare (("b", 0), default_decl, None);
        CPO.Assign (Synth, (indexing_label, 1), end_quals, 
          PO.Iexpr (a, b));
        CPO.Assign (Synth, (fn_call_label, 1), 
          rand_quals, 
          PO.Aexpr (PO.CustomNumber (
            "fn", ["arg1", fv1], Some rand_info)));
        CPO.Assign (Source, ("foo", 1), rand_quals, 
          PO.Aexpr (PO.Abinop (PO.Sum, 
            PO.PONumber (Oratio.ReducedRatio (10, 1)), 
            fv2)));
        CPO.Return CPO.True
    ]
  ] in 
  (* print_cpoprog is; 
  print_cpoprog should_be; *)
  ast_equal is should_be

let test_guard ctxt = 
  let is = transform_program cfg p19 in 
  let open POCorepo in 
  let open Syntax in 
  let open Oratio in 
  let rand_quals = make_quals ~rand:(Rand ["userid"]) () in 
  let assign_foo_is_zero = Assign (Synth, ("^fvid1", 1), rand_quals, 
    Bexpr (BinNumOp (AEquals, 
        PONumber (ReducedRatio (0, 1)),
        GetNumber (Source, Random, "foo", 1)))) in 
  let should_be = [[
    Assign (Source, ("foo", 1), rand_quals,
      Aexpr (RandomNumber (
        POArray (Number, [
            Aexpr (PONumber (ReducedRatio (1, 3)));
            Aexpr (PONumber (ReducedRatio (1, 3)));
            Aexpr (PONumber (ReducedRatio (1, 3)))]),
        POArray (Number, [
            Aexpr (PONumber (ReducedRatio (0, 1)));
            Aexpr (PONumber (ReducedRatio (1, 1)));
            Aexpr (PONumber (ReducedRatio (2, 1)))]),
        Userid, POString "foo")));
    assign_foo_is_zero;
    Assert (Not (Id ("^fvid1", 1)));
    Assign (Source, ("bar", 1), rand_quals, Sexpr (POString "a"));
    Assign (Synth, ("bar", 3), rand_quals, Sexpr (POString "a"));
    Return True;
  ]; [
    Assign (Source, ("foo", 1), rand_quals,
        Aexpr (RandomNumber (
            POArray (Number, [
                Aexpr (PONumber (ReducedRatio (1, 3)));
                Aexpr (PONumber (ReducedRatio (1, 3)));
                Aexpr (PONumber (ReducedRatio (1, 3)))]),
            POArray (Number, [
                Aexpr (PONumber (ReducedRatio (0, 1)));
                Aexpr (PONumber (ReducedRatio (1, 1)));
                Aexpr (PONumber (ReducedRatio (2, 1)))]),
            Userid, POString "foo")));
    assign_foo_is_zero;
    Assert (Id ("^fvid1", 1)); 
    Assign (Source, ("bar", 2), rand_quals, Sexpr (POString "b"));
    Assign (Synth, ("bar", 3), rand_quals, Sexpr (POString "b"));
    Return True]
  ] in 
  (*print_POCorepo_ast is;*)
  ast_equal is should_be

let test_transform_trivial ctxt = 
    let is = transform_program cfg p25 in 
    let open CPO in 
    let open Po_basetypes in 
    let should_be = [
        [Assign (Source, ("title", 1), 
          make_quals ~rand:(Rand ["userid"]) (), 
          PO.Bexpr (PO.RandomBoolean (
                PO.POArray (Number, []),
                PO.POArray (Boolean, []),
                PO.Userid, 
                PO.POString "title")));
         Return True]
    ] in 
    ast_equal is should_be

let test_type_conversion ctxt = 
  let open Po_syntax in 
  let label_userid = "userid" in 
  let get_userid = GetNumber (ExtSource, External, label_userid, 0) in 
  let userid_is_zero = BinNumOp (AEquals, PONumber Oratio.zero, get_userid) in 
  let userid_map = POMap (Number, POMap_.empty
    |> POMap_.add "1234" (Aexpr (PONumber Oratio.one))) in 
  assert_raises
    ~msg:"in_whitelist first assigned to a number, then a boolean."
    (Syntax.TypeError (Number, Boolean, Bexpr (BinBinOp (And, 
        Not (userid_is_zero), BIexpr (userid_map, Aexpr get_userid)))))
    (fun _ -> transform_program cfg p24)

let test_transform_trivial ctxt = 
    let is = transform_program cfg p25 in 
    let open CPO in 
    let open Po_basetypes in 
    let should_be = [
        [Assign (Source, ("title", 1), 
          make_quals ~rand:(Rand ["userid"]) (), 
          PO.Bexpr (PO.RandomBoolean (
            PO.POArray (Number, []),
            PO.POArray (Boolean, []),
            PO.Userid, 
            PO.POString "title")));
         Return True]
    ] in 
    ast_equal is should_be

let test_unmoored ctxt = 
    (* This is no longer supported in current versions of the compiler. *)
    (*let p = "a = 1;
    if (foo) {
        foo || bar;
        return false;
    }" in *)
    let open Syntax in 
    let offending_line = Bexpr (BinBinOp (Or,
        GetBoolean (ExtSource, External, "foo", 0),
        GetBoolean (ExtSource, External, "bar", 0))) in
    (*assert_raises 
        ~msg:"Second line should raise error."
        (StaticErrors.make_conversion_error offending_line)
        (fun _ -> transform_program cfg p)*)
    ignore (offending_line)

let test_icse_example ctxt = 
    let cfg = POConfig.load_annotations_json "{deviceid : {
              card : \"high\"
          },
          userid : {
              card : \"high\"
          },
          getContext : {
              dynamism : \"tv\"
          },
          getBanditWeights : {
              randomness : \"rand\",
              unit : \"userid\",
              dynamism : \"tv\"
          },
          getBanditChoices : {
              randomness : \"det\",
              corr_t : \"(some exo)\",
              dynamism : \"tv\"
          }
      }" in 
    let is = transform_program cfg icse_example in 
    let open CPO in 
    let open PO in 
    let unit_quals = make_quals ~card:High ~corr:End () in 
    let rand_quals = make_quals ~rand:(Rand ["userid"]) () in     
    (* declarations *)
    let decl_choices = 
        Declare (("choices", 0), default_decl, None) in 
    let decl_country = 
        Declare (("country", 0), default_decl, Some Smtlib.string_sort) in 
    let decl_deviceid = Declare (("deviceid", 0), unit_quals, None) in 
    let decl_userid = Declare (("userid", 0), unit_quals, None) in 
    let decl_weights = 
        Declare (("weights", 0), default_decl, None) in 
    let declarations = [decl_choices; decl_country; decl_deviceid; decl_userid; 
      decl_weights] in 
    (* external gets *)
    let get_deviceid = Get (ExtSource, External, "deviceid", 0) in 
    let get_userid = Get (ExtSource, External, "userid", 0) in 
    let get_country = GetString (ExtSource, External, "country", 0) in 
    (* assign dynamic_policy *)
    let label_dynamic_policy = "dynamic_policy" in 
    let dynamic_policy = Bexpr (RandomBoolean (
        POArray (Number, [
            Aexpr (PONumber (Oratio.ReducedRatio (7, 10))); 
            Aexpr (PONumber (Oratio.ReducedRatio (3, 10)))]), 
        POArray (Boolean, [
            Bexpr (POBoolean false); 
            Bexpr (POBoolean true)]), 
        Userid, PO.POString label_dynamic_policy)) in
    let assign_dynamic_policy =  
        Assign (Source, (label_dynamic_policy, 1), 
          make_quals ~rand:(Rand ["userid"]) (), 
          dynamic_policy) in 
    (* assign context *)
    let label_context = "context" in 
    let context = CustomExpr ("getContext", [
            ("deviceid", get_deviceid); 
            ("userid", get_userid)], 
        None) in 
    let assign_context = 
        Assign (Source, (label_context, 1), make_quals ~corr:End ~dyn:Tv (), 
            context) in 
    (* assign weights *)
    let label_weights = "weights" in
    let get_weights = GetContainer (Source, Random, label_weights, 1, Number) in 
    let get_weights_ext = 
        GetContainer (ExtSource, External, label_weights, 0, Unknown) in 
    let weights = Cexpr (CustomContainer ("getBanditWeights", [
        "context", Get (Source, Delay, "context", 1)
    ], Unknown, 
        Some {unit_arg="userid";
              unit_value=Userid;
              salt=(POString label_weights)})) in 
    let assign_weights = 
        Assign (Source, (label_weights, 1), 
          make_quals ~rand:(Rand ["userid"]) ~dyn:Tv (), 
          weights) in 
    (* assign choices *)
    let label_choices = "choices" in 
    let get_choices = 
        GetContainer (Source, Delay, label_choices, 1, Number) in 
    let get_choices_ext = 
        GetContainer (ExtSource, External, label_choices, 0, Unknown) in 
    let choices = Cexpr (CustomContainer ("getBanditChoices", [
        ("context", Get (Source, Delay, "context", 1));
        ("userid", get_userid)], 
        Number, None)) in 
    let assign_choices = 
        Assign (Source, (label_choices, 1), 
            make_quals ~dyn:Tv ~rand:(Rand ["userid"]) (), choices) in 
    (* assign max_bitrate_1*)
    let label_max_bitrate = "max_bitrate" in 
    let get_max_bitrate_1 = GetNumber (Source, Random, label_max_bitrate, 1) in 
    let max_bitrate_1 = Aexpr (RandomNumber (get_weights, 
        get_choices, Userid, PO.POString label_max_bitrate)) in 
    let assign_max_bitrate_1 = 
        Assign (Source, (label_max_bitrate, 1), 
          make_quals ~rand:(Rand ["userid"]) ~dyn:Tv (), 
          max_bitrate_1) in 
    (* assign emerging_market *)
    let label_country_is_brazil = prefix ^ "1" in 
    let label_country_is_india = prefix ^ "2" in 
    let label_emerging_market = "emerging_market" in 
    let get_country_is_brazil = 
      GetBoolean (Synth, Delay, label_country_is_brazil, 1) in 
    let get_country_is_india = 
      GetBoolean (Synth, Delay, label_country_is_india, 1) in 
    let country_is_brazil = Bexpr (BinStrOp (SEquals, 
      get_country, POString "BR")) in 
    let country_is_india =  Bexpr (BinStrOp (SEquals, 
      get_country, POString "IN")) in 
    let emerging_market = Bexpr (BinBinOp (Or, 
      get_country_is_india, get_country_is_brazil)) in

    let country_quals = make_quals ~corr:End () in 
    
    let assign_country_is_india = Assign (Synth, (label_country_is_india, 1), 
        country_quals, country_is_india) in
    let assign_country_is_brazil = Assign (Synth, (label_country_is_brazil, 1), 
        country_quals, country_is_brazil) in 
    
    let assign_emerging_market = Assign (Source, (label_emerging_market, 1), 
        country_quals, emerging_market) in 
    (* assign established market *)
    let label_country_is_canada = prefix ^ "3" in 
    let label_country_is_us = prefix ^ "4" in 
    let label_established_market = "established_market" in 
    let get_country_is_us = 
      GetBoolean (Synth, Delay, label_country_is_us, 1) in 
    let get_country_is_canada = 
      GetBoolean (Synth, Delay, label_country_is_canada, 1) in 
    let country_is_canada = Bexpr (BinStrOp (SEquals, 
      get_country, POString "CA")) in 
    let country_is_us = Bexpr (BinStrOp (SEquals, 
      get_country, POString "US")) in 
    let established_market = Bexpr (BinBinOp (Or,
      get_country_is_us, get_country_is_canada)) in
    
    let assign_country_is_canada = Assign (Synth, (label_country_is_canada, 1), 
      country_quals, country_is_canada) in 
    let assign_country_is_us = Assign (Synth, (label_country_is_us, 1), 
      country_quals, country_is_us) in 
    let assign_established_market = Assign (Source, 
        (label_established_market, 1), 
            country_quals, established_market) in 
    (* assign max_bitrate_2 *)
    let max_bitrate_2 = Aexpr (RandomNumber (
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (9, 10))); 
        Aexpr (PONumber (Oratio.ReducedRatio (1, 10)))]),
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (400, 1))); 
        Aexpr (PONumber (Oratio.ReducedRatio (750, 1)))]), 
      Userid, PO.POString label_max_bitrate)) in 
    let get_max_bitrate_2 = GetNumber (Source, Random, label_max_bitrate, 2) in 
    let assign_max_bitrate_2 = Assign (Source, (label_max_bitrate, 2), 
      make_quals ~rand:(Rand ["userid"]) (), max_bitrate_2) in 
    (* assign max_bitrate_3 *)
    let max_bitrate_3 = Aexpr (RandomNumber (
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (1, 2))); 
        Aexpr (PONumber (Oratio.ReducedRatio (1, 2)))]), 
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (400, 1))); 
        Aexpr (PONumber (Oratio.ReducedRatio (750, 1)))]), 
      Userid, PO.POString label_max_bitrate)) in 
    let get_max_bitrate_3 = GetNumber (Source, Random, label_max_bitrate, 3) in 
    let assign_max_bitrate_3 = Assign (Source, (label_max_bitrate, 3), 
      make_quals ~rand:(Rand ["userid"]) (), max_bitrate_3) in 
    (* assign max_bitrate_4 *)
    let max_bitrate_4 = Aexpr (PONumber (Oratio.ReducedRatio (400, 1))) in 
    let assign_max_bitrate_4 = Assign (Source, (label_max_bitrate, 4), 
      rand_quals, max_bitrate_4) in 
    let quals_final_bitrate = make_quals ~rand:(CS {dets=[4]; rands=[
        (1, ["userid"]);
        (2, ["userid"]);
        (3, ["userid"])]}) () in 
    let assign_max_bitrate_5 arg = Assign (Synth, (label_max_bitrate, 5), 
      rand_quals,
      (* make_quals ~rand:(CS {dets=[4]; rands=[
        (3, ["userid"]);
        (2, ["userid"])]
        }) 
        (),  *)
      Aexpr arg) in 
    let assign_max_bitrate_6 arg = Assign (Synth, (label_max_bitrate, 6), 
      (* quals_final_bitrate,  *)
      make_quals ~rand:(Rand ["userid"]) ~dyn:Tv (),
      Aexpr arg) in 
    (* prefixes to all paths *)
    let prefixes = declarations @ [
            assign_dynamic_policy; 
            assign_context;
            assign_country_is_brazil;
            assign_country_is_india;
            assign_emerging_market;
            assign_country_is_canada;
            assign_country_is_us;
            assign_established_market
          ] in     
    (* assign phis *)
    (* let sub_pres = [ assign_country_is_brazil; assign_country_is_india;
      assign_emerging_market; assign_country_is_canada; assign_country_is_us;
      assign_established_market ] in  *)
    let sub_pres = [] in 
    let should_be = [
      prefixes @ [
        Assert (Id (label_dynamic_policy, 1)); 
        assign_weights; assign_choices; 
        assign_max_bitrate_1;
        assign_max_bitrate_6 get_max_bitrate_1;
        Assign (Synth, (label_choices, 2), 
            make_quals ~dyn:Tv ~rand:(Rand["userid"]) (), 
            (* we lose codomain information when evaluating phis *)
            Cexpr (GetContainer (Source, Delay, label_choices, 1, Unknown))); 
        Assign (Synth, (label_weights, 2), 
            make_quals ~dyn:Tv ~rand:(Rand ["userid"]) (),
            (* we lose codomain information when evaluating phis *)
            Cexpr (GetContainer (Source, Random, label_weights, 1, Unknown))); 
        Return True];
      prefixes @ [Assert (Not (Id (label_dynamic_policy, 1)))] @ sub_pres @ [
        Assert (Id (label_emerging_market, 1)); 
        assign_max_bitrate_2;
        assign_max_bitrate_5 get_max_bitrate_2;
        assign_max_bitrate_6 get_max_bitrate_2; 
        Assign (Synth, (label_choices, 2), 
            make_quals ~dyn:Tv ~rand:(Rand ["userid"]) (),
          Cexpr get_choices_ext);
        Assign (Synth, (label_weights, 2), 
            make_quals ~dyn:Tv ~rand:(Rand ["userid"]) (),
            Cexpr get_weights_ext);
        Return True];
      prefixes @ [Assert (Not (Id (label_dynamic_policy, 1)))] @ sub_pres @ [ 
        Assert (And (Id (label_established_market, 1), 
                Not (Id (label_emerging_market, 1)))); 
        assign_max_bitrate_3;
        assign_max_bitrate_5 get_max_bitrate_3;
        assign_max_bitrate_6 get_max_bitrate_3;
        Assign (Synth, (label_choices, 2), 
            make_quals ~dyn:Tv ~rand:(Rand ["userid"]) (),
            Cexpr get_choices_ext); 
        Assign (Synth, (label_weights, 2), 
          make_quals ~dyn:Tv ~rand:(Rand ["userid"]) (),
          Cexpr get_weights_ext); 
        Return True];
      prefixes @ [Assert (Not (Id (label_dynamic_policy, 1)))] @ sub_pres @ [ 
        Assert (Not (Or (Id (label_established_market, 1), 
                         Id (label_emerging_market, 1)))); 
        assign_max_bitrate_4;
        assign_max_bitrate_5 (PONumber (Oratio.ReducedRatio (400, 1)));
        assign_max_bitrate_6 (PONumber (Oratio.ReducedRatio (400, 1))); 
        Assign (Synth, (label_choices, 2), 
          make_quals ~dyn:Tv ~rand:(Rand ["userid"]) (),
          Cexpr 
            (GetContainer (ExtSource, External, label_choices, 0, Unknown))); 
        Assign (Synth, (label_weights, 2), 
          make_quals ~dyn:Tv ~rand:(Rand ["userid"]) (),
          Cexpr 
            (GetContainer (ExtSource, External, label_weights, 0, Unknown))); 
        Return True]] in  
    (* print_cpoprog is; *)
    ast_equal is should_be

let test_phi_nodes ctxt = 
  (* Log.set_log_level Log.DEBUG; *)
    let is = transform_program cfg phi_test in 
    let open CPO in 
    let open Config in 
    let label_launched = "launched" in 
    let label_skip_logging = "skip_logging" in 
    let label_enabled = "enabled" in 
    let label_ep_fdsa = prefix ^ "2" in 
    let label_ep_asdf = prefix ^ "3" in 
    let label_guard = prefix ^ "1" in 
    let label_ep_fn = "externalPredicate" in 
    let label_userid = "userid" in 
    let label_ep = "ep" in 
    let label_use_in_flyout = "use_in_flyout" in 
    let get_userid = PO.GetNumber (ExtSource, PO.External, label_userid, 0) in 
    let decl_quals = make_quals ~corr:End () in 
    let get_ep_asdf = PO.GetBoolean (Synth, PO.Delay, label_ep_asdf, 1) in 
    let get_ep_fdsa = PO.GetBoolean (Synth, PO.Delay, label_ep_fdsa, 1) in 
    let prefix =[
        Declare ((label_launched, 0), decl_quals, Some Smtlib.bool_sort);

        Assign (Source, (label_skip_logging, 1), 
          default_quals, PO.Bexpr (PO.POBoolean false));
        
        Assign (Source, (label_enabled, 1), 
          default_quals, PO.Bexpr (PO.POBoolean false));
        
        Assign (Synth, (label_ep_fdsa, 1), 
          decl_quals, PO.Bexpr (PO.CustomBoolean (label_ep_fn, 
            [(label_userid, PO.Aexpr get_userid); 
             (label_ep, PO.Sexpr (PO.POString "fdsa"))], None)));
        
        Assign (Synth, (label_ep_asdf, 1), 
          decl_quals, PO.Bexpr (PO.CustomBoolean (label_ep_fn, 
            [(label_userid, PO.Aexpr get_userid); 
              (label_ep, PO.Sexpr (PO.POString "asdf"))], None)));
        
        Assign (Synth, (label_guard, 1), 
          decl_quals,
            PO.Bexpr (PO.BinBinOp (PO.Or, get_ep_asdf, PO.Not get_ep_fdsa)))
    ] in 
    let launched = PO.Bexpr (PO.RandomBoolean (
        PO.POArray (PO.Number, [
            PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1,5)));
            PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (4,5)))
        ]),
        PO.POArray (PO.Boolean, [
            PO.Bexpr (PO.POBoolean false); 
            PO.Bexpr (PO.POBoolean true)
        ]),
        PO.Userid, 
        PO.POString label_launched
    )) in 
    let enabled = PO.Bexpr (PO.RandomBoolean (
        PO.POArray (PO.Number, [one_half; one_half]),
        bernoulli_choices,
        PO.Userid, 
        PO.POString label_enabled
    )) in 
    let rand_quals = make_quals ~rand:(Rand [label_userid]) () in 
    let should_be = [
        prefix @ [
            Assert (Id (label_guard, 1));
            Assign (Source, (label_skip_logging, 2), decl_quals,
              PO.Bexpr (PO.POBoolean true));
            Assign (Synth, (label_enabled, 5), rand_quals, 
              PO.Bexpr (PO.POBoolean false));
            Assign (Synth, (label_launched, 2), rand_quals, 
              PO.Bexpr (
                  PO.GetBoolean (ExtSource, PO.External, label_launched, 0)));
            Assign (Synth, (label_skip_logging, 5), rand_quals, 
              PO.Bexpr (PO.POBoolean true));
            Assign (Source, (label_use_in_flyout, 1), rand_quals, 
              PO.Bexpr (PO.POBoolean false));
            Assert True;
            Return False;            
        ];
        prefix @ [
            Assert (Not (Id (label_guard, 1)));
            Assign (Source, (label_launched, 1), rand_quals, launched);
            Assert (Id (label_launched, 1));
            Assign (Source, (label_enabled, 2), rand_quals, 
              PO.Bexpr (PO.POBoolean true));
              Assign (Source, (label_skip_logging, 3), rand_quals, 
              PO.Bexpr (PO.POBoolean true));
            Assign (Synth, (label_skip_logging, 4), rand_quals, 
              PO.Bexpr (PO.POBoolean true));
            Assign (Synth, (label_enabled, 4), rand_quals,
              PO.Bexpr (PO.POBoolean true));
            Assign (Synth, (label_enabled, 5), rand_quals,
              PO.Bexpr (PO.POBoolean true));
            Assign (Synth, (label_launched, 2), rand_quals,
              PO.Bexpr (PO.GetBoolean (Source, PO.Random, label_launched, 1)));
            Assign (Synth, (label_skip_logging, 5), rand_quals, 
              PO.Bexpr (PO.POBoolean true));
            Assign (Source, (label_use_in_flyout, 1), rand_quals, 
              PO.Bexpr (PO.POBoolean true));
            Assert True;
            Return False;            
        ];
        prefix @ [
            Assert (Not (Id (label_guard, 1)));
            Assign (Source, (label_launched, 1), rand_quals, launched);
            Assert (Not (Id (label_launched, 1)));
            Assign (Source, (label_enabled, 3), rand_quals, enabled);
            Assign (Synth, (label_skip_logging, 4), rand_quals, 
              PO.Bexpr (PO.POBoolean false));
            Assign (Synth, (label_enabled, 4), rand_quals,  
              PO.Bexpr (PO.GetBoolean (Source, PO.Random, label_enabled, 3)));
            Assign (Synth, (label_enabled, 5), rand_quals,
              PO.Bexpr (PO.GetBoolean (Source, PO.Random, label_enabled, 3)));
            Assign (Synth, (label_launched, 2), rand_quals,
              PO.Bexpr (PO.GetBoolean (Source, PO.Random, label_launched, 1)));
            Assign (Synth, (label_skip_logging, 5), rand_quals, 
              PO.Bexpr (PO.POBoolean false));
            Assign (Source, (label_use_in_flyout, 1), rand_quals, 
              PO.Bexpr (PO.GetBoolean (Source, PO.Random, label_enabled, 3)));
            Assert True;
            Return True;   
        ]
    ] in 
    (* print_cpoprog is; *)
    ast_equal is should_be


let test_transform_reset_exp ctxt = 
    let is = transform_program cfg reset_exp in 
    let ddg = reset_exp 
        |> make_program cfg 
        |> Normalize.normalize cfg 
        |> snd
        |> DDG.build_dependence_graph in 
    assert_bool "userid should be a node in the DDG"
                (DDG.nodes ddg |> List.mem ("userid", 0));
    let open CPO in 
    let labels_userid = { card=High; dyn=Const; rand=Det; corr=End } in 
    let label_userid = "userid" in 
    let type_userid = Some Smtlib.int_sort in 
    let get_userid = PO.GetNumber (ExtSource, External, label_userid, 0) in 
    let decl_userid = Declare ((label_userid, 0), labels_userid, type_userid) in
    let label_unit = prefix ^ "1" in 
    let expr_unit = PO.Aexpr (PO.Abinop (PO.Product,
                                         PO.PONumber (Oratio.ratio_of_int 2),
                                         get_userid)) in 

    let assign_unit = Assign (Config.Synth, (label_unit, 1), 
        labels_userid, expr_unit) in 
        
    let label_foo = "foo" in 
    let expr_foo = PO.Bexpr (
        PO.RandomBoolean (
            PO.POArray (PO.Number, [
                PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (9, 10)));
                PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 10)))
            ]),
            bernoulli_choices,
            PO.UnitR label_unit,
            PO.POString label_foo
        )
      ) in 
    let assign_foo = Assign (Config.Source, (label_foo, 1), {card=Low; 
        dyn=Const; rand=Rand[label_unit]; corr=Exo}, expr_foo) in 
    let return_true = Return True in 
    let should_be = [[decl_userid; assign_unit; assign_foo; return_true]] in 
    ast_equal is should_be 

let suite = 
    "suite">:::
    [
        "test_transform_straight_line">::test_tranform_straight_line;
        "test_transform_straight_line_with_rv">::test_transform_straight_line_with_rv;
        "test_basic_paths">::test_basic_paths;
        "test_basic_paths_2">::test_basic_paths_2;
        "test_with_fvs_1">::test_with_fvs_1;
        "test_with_fvs_2">::test_with_fvs_2;
        "test_with_fvs_3">::test_with_fvs_3;
        "test_paths_truncate">::test_paths_truncate;
        "test_nested_paths">::test_nested_paths;
        "test_nested_rvs">::test_nested_rvs; 
        "test_with_annotations">::test_with_annotations;
        "test_transform_p12">::test_transform_p12; 
        "test_transform_p6">::test_transform_p6;
        "test_guard">::test_guard; 
        "test_type_conversion">::test_type_conversion;
        "test_transform_trivial">::test_transform_trivial;
        "test_unmoored">::test_unmoored; 
        "test_icse_example">::test_icse_example;
        "test_phi_nodes">::test_phi_nodes; 
        "test_transform_repeat_exp">::test_transform_reset_exp
    ]

let () = 
    Targets.PlanOut.register_printers ();
    Printf.printf "Running %s" __FILE__;
    run_test_tt_main suite