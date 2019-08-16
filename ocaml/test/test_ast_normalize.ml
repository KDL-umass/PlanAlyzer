open OUnit2
open Programs_aux
open Config 

open Mock_targets.PlanOut
open Po_syntax 

let make_program = make_program2 Parse.exec_po_compiler Parse.make_program
let cfg = POConfig.load_annotations_json default_annot
let ast_equal = ast_equal assert_bool 

let print_program ?(show_index=true) p = 
  Printf.printf "\n%s\n" (Ast.Format.string_of_program ~show_index p)

let const_prop p = 
  (POConfig.empty, make_program cfg p) 
  |> Normalize.constant_propagation
  |> snd

let min_prog p = 
  (POConfig.empty, make_program cfg p) 
  |> Normalize.minimize_program 
  |> snd

let cms_prog p = 
  (POConfig.empty, make_program cfg p) 
  |> Normalize.constant_min_steady 
  |> snd

let lin_prog p = 
  let varid = Po_counters.thread_safe_copy 
    ~prefix:Po_counters.pseudo_prefix "varid" in 
  (* let skipid = Po_counters.thread_safe_copy
    ~prefix:Po_counters.pseudo_prefix "skip" in  *)
  (* Po_counters.renew_uid "skipid"; *)
  (POConfig.empty, make_program cfg p) 
  |> Normalize.linearize_fn_app ~varid
  (* |> Normalize.minimize_seqs ~skipid *)
  |> snd  
 
let default_guard_prog p = 
  (POConfig.empty, make_program cfg p) 
  |> Normalize.add_default_guard ~skipid:Po_counters.skipid
  |> snd

let lift_rand_prog p = 
  (POConfig.empty, make_program cfg p) 
  |> Normalize.lift_random_variables ~varid:Po_counters.varid 
  |> snd

let norm_prog cfg p = 
  Normalize.normalize cfg (make_program cfg p) |> snd
  
let test_tree_rewrite_all_null ctxt = 
  let open Normalize in 
  let efn e = Null in 
  let is = make_program cfg p1 |> tree_rewrite ~efn in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, Null);
    Assignment (Source, "bar", 1, Null);
    Assignment (Source, "baz", 1, Null);
    Return (BinNumOp (Lt, 
      Abinop (Product, 
        GetNumber (Source, Unclassified, "baz", 1),
        GetNumber (Source, Unclassified, "foo", 1)),
      GetNumber (Source, Unclassified, "bar", 1)))]) in 
  assert_equal is should_be

let test_tree_rewrite_null_numbers ctxt = 
  let afn e = NullNumber in 
  let is = make_program cfg p1 |> Normalize.tree_rewrite ~afn in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, Aexpr NullNumber);
    Assignment (Source, "bar", 1, Aexpr NullNumber);
    Assignment (Source, "baz", 1, Aexpr NullNumber);
    Return (BinNumOp (Lt, NullNumber, NullNumber))]) in 
  assert_equal is should_be

let test_cp_basic_numbers ctxt = 
  let is = const_prop p1 in 
  let ten  = PONumber (Oratio.ratio_of_int 10) in 
  let nine = PONumber (Oratio.ratio_of_int 9) in
  let trty = PONumber (Oratio.ratio_of_int 30) in  
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, Aexpr ten);
    Assignment (Source, "bar", 1, Aexpr (Abinop (Product, ten, nine)));
    Assignment (Source, "baz", 1, Aexpr trty);
    Return (BinNumOp (Lt, 
      Abinop (Product, trty, ten), 
      GetNumber (Source, Unclassified, "bar", 1)))]) in
  ast_equal is should_be

let test_cp_basic_containers ctxt = 
  let is = const_prop p2 in 
  let w1 = PONumber (Oratio.ratio_of_int 10) in 
  let w2 = PONumber (Oratio.ReducedRatio (2, 5)) in 
  let c1 = POString "asdf" in 
  let c2 = POBoolean true in 
  let should_be = Program (Seq [
    Assignment (Source, "weights", 1, Cexpr (
      POArray (Unknown, [Aexpr w1; Aexpr w2]))); 
    Assignment (Source, "choices", 1, Cexpr (
      POArray (Unknown, [Sexpr c1; Bexpr c2])));
    Assignment (Source, "foo", 1, RandomVar (
      POArray (Unknown, [Aexpr w1; Aexpr w2]), (* Type doesn't 
      propagate; just being rewritten. *)
      POArray (Unknown, [Sexpr c1; Bexpr c2]),
      Userid, 
      POString "foo"))
  ]) in 
  assert_equal is should_be

let test_cp_with_phi ctxt = 
  let is = const_prop p3 in 
  let ten = PONumber (Oratio.ratio_of_int 10) in 
  let twn = PONumber (Oratio.ratio_of_int 20) in 
  let assign_foo_1 = Assignment (Source, "foo", 1, Aexpr ten) in 
  let assign_foo_2 = Assignment (Source, "foo", 2, 
                Aexpr (Abinop (Product, ten, twn))) in 
  (* types not yet propagated. *)
  let assign_foo_phi = Assignment (Synth, "foo", 3, 
    Phi (Unknown, "foo", [2; 1])) in 
  let should_be = Program (Seq [
    assign_foo_1;
    Seq [Cond [(Guard (GetBoolean (ExtSource, External, "asdf", 0)),
         Seq [assign_foo_2])];
       assign_foo_phi];
    Assignment (Source, "bar", 1, Aexpr (Abinop (Product,
      GetNumber (Synth, Unclassified, "foo", 3),
      GetNumber (Synth, Unclassified, "foo", 3))))
  ]) in 
  ast_equal is should_be

let test_min_prog_basic ctxt = 
  let is = min_prog p4 in 
  let one = PONumber (Oratio.ratio_of_int 1) in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, Aexpr one);
    Assignment (Source, "bar", 1, Sexpr (POString "b"));
    Seq [Cond [(Guard (POBoolean true),
          Seq [Return (POBoolean false)])]]
  ]) in 
  ast_equal is should_be

let test_min_fully_1 ctxt = 
  let is = cms_prog p1 in 
  let ten  = PONumber (Oratio.ratio_of_int 10) in 
  let trty = PONumber (Oratio.ratio_of_int 30) in  
  let nnty = PONumber (Oratio.ratio_of_int 90) in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, Aexpr ten);
    Assignment (Source, "bar", 1, Aexpr nnty);
    Assignment (Source, "baz", 1, Aexpr trty);
    Return (POBoolean false)]) in
  assert_equal is should_be

let test_min_fully_2 ctxt = 
  let is = cms_prog p3 in 
  let ten = PONumber (Oratio.ratio_of_int 10) in 
  let twn = PONumber (Oratio.ratio_of_int 200) in 
  let assign_foo_1 = Assignment (Source, "foo", 1, Aexpr ten) in 
  let assign_foo_2 = Assignment (Source, "foo", 2, Aexpr twn) in 
  (* Types not yet propagated *)
  let assign_foo_phi = 
    Assignment (Synth, "foo", 3, Phi (Unknown, "foo", [2; 1])) in 
  let should_be = Program (Seq [
    assign_foo_1;
    Seq [Cond [(Guard (GetBoolean (ExtSource, External, "asdf", 0)),
          Seq [assign_foo_2])];
       assign_foo_phi];
    Assignment (Source, "bar", 1, Aexpr (Abinop (Product,
      GetNumber (Synth, Unclassified, "foo", 3),
      GetNumber (Synth, Unclassified, "foo", 3))))
  ]) in 
  ast_equal is should_be

let test_linearize_type_unknown ctxt = 
  let is = lin_prog p5 in 
  let should_be = Program (Seq [
    Assignment (Synth, prefix ^ "1", 1, 
      Iexpr (GetContainer (ExtSource, External, "a", 0, Unknown),
           Get (ExtSource, External, "b", 0)));
    Assignment (Source, "foo", 1, 
      CustomExpr ("fn", 
        [("arg1", Get (Synth, Unclassified, prefix ^ "1", 1))], 
        None))
  ]) in 
  ast_equal is should_be

let test_linearize_number ctxt = 
  let is = lin_prog p6 in 
  let label_arg1 = prefix ^ "1" in 
  let arg1 = Iexpr (
    GetContainer (ExtSource, External, "a", 0, Unknown), 
    Get (ExtSource, External, "b", 0)) in 
  let get_arg1 = Get (Synth, Unclassified, label_arg1, 1) in
  let label_arg2 = prefix ^ "2" in 
  let arg2 = Aexpr (CustomNumber ("fn", 
      [("arg1", get_arg1);
       ("arg2", Get (ExtSource, External, "fooid", 0))],
    None)) in 
  let get_arg2 = GetNumber (Synth, Unclassified, label_arg2, 1) in  
  let foo = Aexpr (Abinop (Sum, 
    get_arg2, 
    PONumber (Oratio.ratio_of_int 10))) in 
  let should_be = Program (Seq [
    Assignment (Synth, label_arg1, 1, arg1);
    Assignment (Synth, label_arg2, 1, arg2);
    Assignment (Source, "foo", 1, foo)
  ]) in 
  (*print_ast is;
  print_ast should_be;*)
  ast_equal is should_be

let test_extract_iexprs ctxt = 
  (* foo = a[b % length(a)][c][d]; 

    should be converted to 

     fv1 = length(a);    => fv2 = length(a);
     fv2 = b % fv1;    => fv3 = b % fv2;
     fv3 = a[fv2];     => fv4 = a[fv3];
     fv4 = fv3[c];     => fv5 = fv4[c];
     foo = fv4[d];     => foo = fv5[d];
  *)
  let is = lin_prog p7 in 
  let a = GetContainer (ExtSource, External, "a", 0, Unknown) in 
  let b = GetNumber (ExtSource, External, "b", 0) in 
  let c = Get (ExtSource, External, "c", 0) in 
  let d = Get (ExtSource, External, "d", 0) in 
  let fv1s = prefix ^ "1" in 
  let fv2s = prefix ^ "2" in 
  let fv3s = prefix ^ "3" in 
  let fv4s = prefix ^ "4" in 
  let fv1 = GetNumber (Synth, Unclassified, fv1s, 1) in 
  let fv2 = Get (Synth, Unclassified, fv2s, 1) in 
  let fv3 = GetContainer(Synth, Unclassified, fv3s, 1, Container) in 
  let fv4 = GetContainer (Synth, Unclassified, fv4s, 1, Unknown) in 
  let stmt1 = Assignment (Synth, fv1s, 1, Aexpr (Length a)) in 
  let stmt2 = Assignment (Synth, fv2s, 1, Aexpr (Abinop (Mod, b, fv1))) in 
  let stmt3 = Assignment (Synth, fv3s, 1, Cexpr (CIexpr (a, fv2))) in 
  let stmt4 = Assignment (Synth, fv4s, 1, Cexpr (CIexpr (fv3, c))) in 
  let stmt5 = Assignment (Source, "foo", 1, Iexpr (fv4, d)) in 
  let should_be = Program (Seq [
    stmt1; stmt2; stmt3; stmt4; stmt5
  ]) in 
  let prog = (match is with 
        | Program (Seq seqs) -> seqs 
        | _ -> assert false) in 
  (*print_ast is;
  print_ast should_be;*)
  assert_equal (List.nth prog 0) stmt1;
  assert_equal (List.nth prog 1) stmt2;
  ast_equal is should_be

let test_extract_rels_from_guards ctxt = 
  let is = lin_prog p8 in 
  let fv1s = prefix ^ "1" in 
  let fv2s = prefix ^ "2"  in 
  let a = Get (ExtSource, External, "a", 0) in 
  let b = Get (ExtSource, External, "b", 0) in 
  let get_asdf = GetBoolean (ExtSource, External, "asdf", 0) in 
  let get_a_equals_b = GetBoolean (Synth, Unclassified, fv2s, 1) in 
  let get_guard = GetBoolean (Synth, Unclassified, fv1s, 1) in
  let should_be = Program (Seq [
    Assignment (Synth, fv2s, 1, Bexpr (Equals (a, b)));
    Assignment (Synth, fv1s, 1, Bexpr (BinBinOp (And, 
      get_asdf, get_a_equals_b)));
    Cond [(Guard get_guard, 
           Seq [Return (POBoolean false)])];
    Return (POBoolean true)]) in 
  (* print_program is;
  print_ast is;
  print_program should_be;
  print_ast should_be; *)
  ast_equal is should_be

let test_extract_fns_from_guards ctxt = 
  let is = lin_prog p9 in 
  let a = GetNumber (ExtSource, External, "a", 0) in 
  let b = GetNumber (ExtSource, External, "b", 0) in 
  let c = GetContainer (ExtSource, External, "c", 0, Unknown) in 
  let label_b_is_zero = prefix ^ "4" in
  let label_a_is_zero = prefix ^ "5" in 
  let label_ab_are_zero = prefix ^ "3" in 
  let label_length_c = prefix ^ "6" in 
  let label_length_c_gt_1 = prefix ^ "1" in 
  let label_fn_arg_42 = prefix ^ "2" in 
  let get_b_is_zero = GetBoolean (Synth, Unclassified, label_b_is_zero, 1) in 
  let get_a_is_zero = GetBoolean (Synth, Unclassified, label_a_is_zero, 1) in 
  let get_ab_are_zero = 
    GetBoolean (Synth, Unclassified, label_ab_are_zero, 1) in 
  let fv3 = GetNumber (Synth, Unclassified, label_length_c, 1) in 
  let fv5 = CustomBoolean ("fn", 
    [("arg1", Aexpr (PONumber (Oratio.ratio_of_int 42)))], 
    None) in 
  let assign_a_is_zero = Assignment (Synth, label_a_is_zero, 1, 
    Bexpr (BinNumOp (AEquals, PONumber Oratio.zero, a))) in 
  let assign_b_is_zero = Assignment (Synth, label_b_is_zero, 1, 
    Bexpr (BinNumOp (AEquals, PONumber Oratio.zero, b))) in 
  let assign_ab_guard = Assignment (Synth, label_ab_are_zero, 1,
    Bexpr (BinBinOp (And, get_a_is_zero, get_b_is_zero))) in 
  let assign_length_c = Assignment (Synth, label_length_c, 1, 
    Aexpr (Length c)) in 
  let should_be = Program (Seq [
    assign_b_is_zero;
    assign_a_is_zero;
    assign_ab_guard;
    Cond [(Guard get_ab_are_zero, Seq [
      assign_length_c;
      Assignment (Synth, label_length_c_gt_1, 1, 
        Bexpr (BinNumOp (Gt, fv3, PONumber Oratio.one)));
      Assignment (Synth, label_fn_arg_42, 1, 
        Bexpr fv5);
      Cond [
      (Guard (GetBoolean (Synth, Unclassified, label_length_c_gt_1, 1)), 
       Seq [Return (POBoolean true)]);
      (Guard (GetBoolean (Synth, Unclassified, label_fn_arg_42, 1)), 
       Seq [Return (POBoolean false)]);
      (Guard (POBoolean true), 
       Seq [Return (POBoolean true)])]
    ])]
  ]) in 
  (* print_program p9; *)
  (* print_program is; *)
  (* print_program should_be; *)
  (* print_ast is; *)
  (* print_ast should_be; *)
  ast_equal is should_be

let test_add_default_guard ctxt = 
  let is = default_guard_prog p3 in 
  let assign_foo_1 = Assignment (Source, "foo", 1, 
    Aexpr (PONumber (Oratio.ratio_of_int 10))) in 
  let assign_foo_2 = Assignment (Source, "foo", 2, Aexpr 
    (Abinop (Product, 
         GetNumber (Source, Unclassified, "foo", 1),
         PONumber (Oratio.ratio_of_int 20)))) in 
  (* Types not yet assigned *)
  let assign_foo_phi = Assignment (Synth, "foo", 3, 
    Phi (Unknown, "foo", [2;1])) in 
  let should_be = Program (Seq [
    assign_foo_1;
    Cond [(Guard (BinBinOp (And, 
         GetBoolean (ExtSource, External, "asdf", 0),
         Not (POBoolean false))), 
         Seq [ assign_foo_2 ]);
        (Guard (BinBinOp (And,
         POBoolean true,
         Not (BinBinOp (Or, 
            GetBoolean (ExtSource, External, "asdf", 0),
            POBoolean false)))),
        Skip "1")];
    assign_foo_phi;
    Assignment (Source, "bar", 1,
      Aexpr (Abinop (Product,
        GetNumber (Synth, Unclassified, "foo", 3),
        GetNumber (Synth, Unclassified, "foo", 3))))
  ]) in 
  (*print_ast is;
  print_ast should_be;*)
  ast_equal is should_be

let test_lift_random_vars ctxt = 
  let is = lift_rand_prog p10 in 
  let should_be = Program (Seq [
    Assignment (Source, "weights", 1, Cexpr
      (POArray (Unknown, [
        Cexpr (POArray (Unknown, [
          Aexpr (PONumber (Oratio.ReducedRatio (1, 10))); 
          Aexpr (PONumber (Oratio.ReducedRatio (1, 5)))
        ]));
        Cexpr (POArray (Unknown, [
          Aexpr (PONumber (Oratio.ReducedRatio (3, 10)));
          Aexpr (PONumber (Oratio.ReducedRatio (2, 5)))
        ]))
      ])));
    Assignment (Source, "choices", 1, Cexpr 
      (POArray (Unknown, [
        Cexpr (POArray (Unknown, [
          Aexpr (PONumber (Oratio.ReducedRatio (4, 1)));
          Aexpr (PONumber (Oratio.ReducedRatio (3, 1)))
        ]));
        Cexpr (POArray (Unknown, [
          Aexpr (PONumber (Oratio.ReducedRatio (2, 1)));
          Aexpr (PONumber (Oratio.ReducedRatio (1, 1)))
        ]))
      ])));
    Assignment (Synth, "bar", 1, RandomVar (
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (1, 2)));
        Aexpr (PONumber (Oratio.ReducedRatio (1, 2)))]),
      POArray (Boolean, [
        Bexpr (POBoolean false);
        Bexpr (POBoolean true)
      ]),
      Userid, 
      POString "bar"
    ));
    Assignment (Synth, "baz", 1, RandomVar (
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (2, 5)));
        Aexpr (PONumber (Oratio.ReducedRatio (3, 5)))]),
      POArray (Boolean, [
        Bexpr (POBoolean false);
        Bexpr (POBoolean true)
      ]),
      Userid, 
      POString "baz"
    ));
    Assignment (Source, "foo", 1, RandomVar (
      CIexpr (
        GetContainer (Source, Unclassified, "weights", 1, Unknown),
        Get (Synth, Random, "bar", 1)),
      CIexpr (
        GetContainer (Source, Unclassified, "choices", 1, Unknown),
        Get (Synth, Random, "baz", 1)),
      Userid,
      POString "foo"
    ))
  ]) in 
  (*print_program (Ast.Format.string_of_program is);
  print_ast is;
  print_ast should_be;*)
  ast_equal is should_be

let test_normalize_p1 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p1) |> snd in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, 
      Aexpr (PONumber (Oratio.ratio_of_int 10)));
    Assignment (Source, "bar", 1, 
      Aexpr (PONumber (Oratio.ratio_of_int 90)));
    Assignment (Source, "baz", 1, 
      Aexpr (PONumber (Oratio.ratio_of_int 30)));
    Return (POBoolean false)
  ]) in 
  (*print_program p1;
  print_ast is;
  print_ast should_be;*)
  assert_equal is should_be

let test_normalize_p2 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p2) |> snd in 
  let w1 = PONumber (Oratio.ratio_of_int 10) in 
  let w2 = PONumber (Oratio.ReducedRatio (2, 5)) in 
  let c1 = POString "asdf" in 
  let c2 = POBoolean true in 
  let should_be = Program (Seq [
    Assignment (Source, "weights", 1, Cexpr (
      POArray (Number, [Aexpr w1; Aexpr w2])));
    Assignment (Source, "choices", 1, Cexpr (
      POArray (Unknown, [Sexpr c1; Bexpr c2])));
    Assignment (Source, "foo", 1, RandomVar (
      POArray (Number, [Aexpr w1; Aexpr w2]), 
      POArray (Unknown, [Sexpr c1; Bexpr c2]),
      Userid, 
      POString "foo"))
  ]) in 
  (*print_ast is;
  print_ast should_be;*)
  assert_equal is should_be 

let test_normalize_p3 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p3) |> snd in 
  let assign_foo_phi = 
    Assignment (Synth, "foo", 3, Phi (Number, "foo", [2; 1])) in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, 
      Aexpr (PONumber (Oratio.ratio_of_int 10)));
    Cond [
      (Guard (GetBoolean (ExtSource, External, "asdf", 0)),
       Assignment (Source, "foo", 2, 
         Aexpr (PONumber (Oratio.ratio_of_int 200))));
      (Guard (Not (GetBoolean (ExtSource, External, "asdf", 0))),
       Skip "1")];
    assign_foo_phi;
    Assignment (Source, "bar", 1,
      Aexpr (Abinop (Product,
        GetNumber (Synth, Delay, "foo", 3),
        GetNumber (Synth, Delay, "foo", 3)
      )))
  ]) in 
  (*print_ast is;
  print_ast should_be;*)
  ast_equal is should_be

let test_normalize_p4 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p4) |> snd in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, Aexpr (PONumber Oratio.one));
    Assignment (Source, "bar", 1, Sexpr (POString "b"));
    Cond [ 
      (Guard (POBoolean true), Return (POBoolean false))
      (* Note: because we minimize, this assumes that the only guard is the
        default guard. This is okay. *)
      (*(Guard (POBoolean false), Skip "1")*)
    ]
  ]) in 
  (*print_ast is;
  print_ast should_be;*)
  assert_equal is should_be

let test_normalize_p5 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p5) |> snd in 
  let fv1s = prefix ^ "1" in 
  let should_be = Program (Seq [
    Assignment (Synth, fv1s, 1, 
      Iexpr (GetContainer (ExtSource, External, "a", 0, Unknown),
           Get (ExtSource, External, "b", 0)));
    Assignment (Source, "foo", 1, 
      CustomExpr ("fn", [("arg1", Get (Synth, Delay, fv1s, 1))], None))
  ]) in 
  (*print_ast is;
  print_ast should_be;*)
  assert_equal is should_be

let test_p5_unit_fail ctxt = 
  let cfg = POConfig.load_annotations_json 
    "{fn : {randomness : \"rand\"}}" in 
  assert_raises (Parse.make_missing_unit_err ~fn:"fn" ~unit:"unit")
    (fun () -> Normalize.normalize cfg (make_program cfg p5))

let test_normalize_p5_annot ctxt = 
  let cfg = POConfig.load_annotations_json 
    "{fn : {randomness : \"rand\", unit: \"arg1\"}}" in 
  let fv1 = Iexpr (
        GetContainer (ExtSource, External, "a", 0, Unknown), 
        Get (ExtSource, External, "b", 0)) in 
  assert_raises 
  (Parse.Malformed_unit fv1)
  (fun () -> Normalize.normalize cfg (make_program cfg p5))

let test_normalize_p6 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p6) |> snd in 
  let fv1s = prefix ^ "1" in 
  let fv2s = prefix ^ "2" in 
  let should_be = Program (Seq [
    Assignment (Synth, fv1s, 1, 
      Iexpr (GetContainer (ExtSource, External, "a", 0, Unknown),
           Get (ExtSource, External, "b", 0)));
    Assignment (Synth, fv2s, 1, 
      Aexpr (CustomNumber ("fn", 
        [("arg1", Get (Synth, Delay, fv1s, 1));
         ("arg2", Get (ExtSource, External, "fooid", 0))], 
         None)));
    Assignment (Source, "foo", 1, 
      Aexpr (Abinop (Sum, 
               PONumber (Oratio.ratio_of_int 10),
               GetNumber (Synth, Delay, fv2s, 1))))
  ]) in 
  (*print_ast is;
  print_ast should_be;*)
  ast_equal is should_be

let test_normalize_p7 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p7) |> snd in 
  let a = GetContainer (ExtSource, External, "a", 0, Container) in 
  let b = GetNumber (ExtSource, External, "b", 0) in 
  let c = Get (ExtSource, External, "c", 0) in 
  let d = Get (ExtSource, External, "d", 0) in 
  let fv1s = prefix ^ "1" in 
  let fv2s = prefix ^ "2" in 
  let fv3s = prefix ^ "3" in 
  let fv4s = prefix ^ "4" in 
  let fv1 = GetNumber (Synth, Delay, fv1s, 1) in 
  let fv2 = GetNumber (Synth, Delay, fv2s, 1) in 
  let fv3 = GetContainer(Synth, Delay, fv3s, 1, Container) in 
  let fv4 = GetContainer (Synth, Delay, fv4s, 1, Unknown) in 
  let stmt1 = Assignment (Synth, fv1s, 1, Aexpr (Length a)) in 
  let stmt2 = Assignment (Synth, fv2s, 1, Aexpr (Abinop (Mod, b, fv1))) in 
  let stmt3 = Assignment (Synth, fv3s, 1, Cexpr (CIexpr (a, Aexpr fv2))) in 
  let stmt4 = Assignment (Synth, fv4s, 1, Cexpr (CIexpr (fv3, c))) in 
  let stmt5 = Assignment (Source, "foo", 1, Iexpr (fv4, d)) in 
  let should_be = Program (Seq [
    stmt1; stmt2; stmt3; stmt4; stmt5
  ]) in 
  (*print_ast is;
  print_ast should_be;*)
  ast_equal is should_be

let test_normalize_p8 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p8) |> snd in 
  let label_a_equals_b = prefix ^ "2" in 
  let label_guard = prefix ^ "1" in 
  let a = Get (ExtSource, External, "a", 0) in 
  let b = Get (ExtSource, External, "b", 0) in 
  let get_asdf = GetBoolean (ExtSource, External, "asdf", 0) in 
  let get_a_equals_b = GetBoolean (Synth, Delay, label_a_equals_b, 1) in 
  let get_guard = GetBoolean (Synth, Delay, label_guard, 1) in 
  let should_be = Program (Seq [
    Assignment (Synth, label_a_equals_b, 1, Bexpr (Equals (a, b)));
    Assignment (Synth, label_guard, 1, Bexpr (BinBinOp (And, 
      get_asdf, get_a_equals_b)));
    Cond [
      (Guard get_guard, Return (POBoolean false));
      (Guard (Not get_guard), Skip "1")
    ];
    Return (POBoolean true)]) in 
  (* print_program is; print_program should_be; *)
  (* print_ast is;
  print_ast should_be; *)
  ast_equal is should_be

let test_normalize_p9 ctxt = 
  let is = Normalize.normalize POConfig.empty (make_program cfg p9) |> snd in 
  let a = GetNumber (ExtSource, External, "a", 0) in 
  let b = GetNumber (ExtSource, External, "b", 0) in 
  let c = GetContainer (ExtSource, External, "c", 0, Unknown) in 
  let label_b_is_zero = prefix ^ "4" in
  let label_a_is_zero = prefix ^ "5" in
  let label_ab_are_zero = prefix ^ "3" in  
  let label_length_c = prefix ^ "6" in 
  let label_length_c_gt_1 = prefix ^ "1" in 
  let label_fn_arg142 = prefix ^ "2" in 
  let get_b_is_zero = GetBoolean (Synth, Delay, label_b_is_zero, 1) in 
  let get_a_is_zero = GetBoolean (Synth, Delay, label_a_is_zero, 1) in 
  let get_ab_are_zero = GetBoolean (Synth, Delay, label_ab_are_zero, 1) in 
  let get_length_c = GetNumber (Synth, Delay, label_length_c, 1) in
  let get_length_c_gt_1 = GetBoolean (Synth, Delay, label_length_c_gt_1, 1) in
  let get_fn_arg142 = GetBoolean (Synth, Delay, label_fn_arg142, 1) in 
  let custom_exp = CustomBoolean ("fn", 
    [("arg1", Aexpr (PONumber (Oratio.ratio_of_int 42)))], None) in 
  let ab_are_zero = BinBinOp (And, get_a_is_zero, get_b_is_zero) in 
  let assign_b_is_zero = Assignment (Synth, label_b_is_zero, 1, 
    Bexpr (BinNumOp (AEquals, PONumber Oratio.zero, b))) in 
  let assign_a_is_zero = Assignment (Synth, label_a_is_zero, 1, 
    Bexpr (BinNumOp (AEquals, PONumber Oratio.zero, a))) in 
  let assign_guard_1 = Assignment (Synth, label_ab_are_zero, 1, 
    Bexpr ab_are_zero) in 
  let should_be = Program (Seq [
    assign_b_is_zero;
    assign_a_is_zero;
    assign_guard_1;
    Cond [(Guard get_ab_are_zero, Seq [
        Assignment (Synth, label_length_c, 1, Aexpr (Length c));
        Assignment (Synth, label_length_c_gt_1, 1, Bexpr (BinNumOp (Gt,
          get_length_c, PONumber Oratio.one)));
        Assignment (Synth, label_fn_arg142, 1, Bexpr custom_exp);
        Cond [
          (Guard get_length_c_gt_1, Return (POBoolean true));
          (Guard (BinBinOp (And, get_fn_arg142, Not get_length_c_gt_1)), 
           Return (POBoolean false));
          (Guard (Not (BinBinOp (Or, get_fn_arg142, get_length_c_gt_1))), 
           Return (POBoolean true))]]);
        (Guard (Not get_ab_are_zero), Skip "1")]
  ]) in 
  (* print_program is; print_program should_be; *)
  (* print_ast is; *)
  (* print_ast should_be; *)
  ast_equal is should_be

let test_normalize_p10 ctxt =
  let prog = make_program cfg p10 in
  let is = Normalize.normalize POConfig.empty prog |> snd in 
  let weights = POArray (Container, [
        Cexpr (POArray (Number, [
          Aexpr (PONumber (Oratio.ReducedRatio (1, 10))); 
          Aexpr (PONumber (Oratio.ReducedRatio (1, 5)))
        ]));
        Cexpr (POArray (Number, [
          Aexpr (PONumber (Oratio.ReducedRatio (3, 10)));
          Aexpr (PONumber (Oratio.ReducedRatio (2, 5)))
        ]))
      ]) in 
  let choices = POArray (Container, [
        Cexpr (POArray (Number, [
          Aexpr (PONumber (Oratio.ReducedRatio (4, 1)));
          Aexpr (PONumber (Oratio.ReducedRatio (3, 1)))
        ]));
        Cexpr (POArray (Number, [
          Aexpr (PONumber (Oratio.ReducedRatio (2, 1)));
          Aexpr (PONumber (Oratio.ReducedRatio (1, 1)))
        ]))
      ]) in 
  let should_be = Program (Seq [
    Assignment (Source, "weights", 1, Cexpr weights);
    Assignment (Source, "choices", 1, Cexpr choices);
    Assignment (Synth, "bar", 1, Bexpr (RandomBoolean (
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (1, 2)));
        Aexpr (PONumber (Oratio.ReducedRatio (1, 2)))]),
      POArray (Boolean, [
        Bexpr (POBoolean false);
        Bexpr (POBoolean true)
      ]),
      Userid, 
      POString "bar"
     )));
    Assignment (Synth, "baz", 1, Bexpr (RandomBoolean (
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (2, 5)));
        Aexpr (PONumber (Oratio.ReducedRatio (3, 5)))]),
      POArray (Boolean, [
        Bexpr (POBoolean false);
        Bexpr (POBoolean true)
      ]),
      Userid, 
      POString "baz"
     )));
    Assignment (Source, "foo", 1, Aexpr (RandomNumber (
      CIexpr (weights, Bexpr (GetBoolean (Synth, Random, "bar", 1))),
      CIexpr (choices, Bexpr (GetBoolean (Synth, Random, "baz", 1))),
      Userid,
      POString "foo"
    )))
  ]) in 
  (* print_program is;
  print_program should_be; *)
  (*print_ast is;*)
  (*print_ast should_be;*)
  ast_equal is should_be

let p11 = "if (foo == \"a\") {
  return true;
  }"

let test_normalize_p11 ctxt =
  let prog = make_program cfg p11 in
  let is = Normalize.normalize POConfig.empty prog |> snd in 
  let should_be = Program (Seq[
    Assignment (Synth, prefix ^ "1", 1, 
      Bexpr (BinStrOp (SEquals,
        GetString (ExtSource, External, "foo", 0),
        POString "a")));
    Cond [
      (Guard (GetBoolean (Synth, Delay, prefix ^ "1", 1)),
       Return (POBoolean true));
      (Guard (Not (GetBoolean (Synth, Delay, prefix ^ "1", 1))),
       Skip "1")
    ]
  ]) in 
  (*print_ast is; 
  print_ast should_be;*)
  ast_equal is should_be

let test_missing_unit_external ctxt = 
  let cfg = POConfig.load_annotations_json
     "{fn : {randomness : \"rand\", codomain : \"number\"} }" in
  assert_raises (Parse.make_missing_unit_err ~fn:"fn" ~unit:"unit")
    (fun () -> 
      make_program cfg p6 
      |> Normalize.normalize cfg)


let test_external_random_var ctxt = 
  let cfg = POConfig.load_annotations_json
    "{a : {randomness : \"rand\", unit: \"whocares\"}}" in 
  let is = norm_prog cfg p9 in 
  let a_zero_label = prefix ^ "5" in 
  let b_zero_label = prefix ^ "4" in 
  let c_length_label = prefix ^ "6" in 
  let c_length_gt_zero_label = prefix ^ "1" in 
  let fn_label = prefix ^ "2" in 
  let a_zero = Bexpr (BinNumOp (AEquals, 
  PONumber (Oratio.ReducedRatio (0, 1)), 
  GetNumber (ExtSource, Random, "a", 0))) in 
  let b_zero = Bexpr (BinNumOp (AEquals, 
  PONumber (Oratio.ReducedRatio (0, 1)), 
  GetNumber (ExtSource, External, "b", 0))) in 
  let c_length = Aexpr (Length (
    GetContainer (ExtSource, External, "c", 0, Unknown))) in 
  let c_length_gt_zero = Bexpr (BinNumOp (Gt, 
         GetNumber (Synth, Delay, c_length_label, 1), 
         PONumber (Oratio.ReducedRatio (1, 1)))) in 
  let fn = Bexpr (CustomBoolean ("fn", 
  [("arg1", Aexpr (PONumber (Oratio.ReducedRatio (42, 1))))], None)) in 
  let label_ab_zero = prefix ^ "3" in 
  let get_a_zero = GetBoolean (Synth, Delay, a_zero_label, 1) in 
  let get_b_zero = GetBoolean (Synth, Delay, b_zero_label, 1) in 
  let ab_zero = BinBinOp (And, get_a_zero, get_b_zero) in 
  let get_ab_zero = GetBoolean (Synth, Delay, label_ab_zero, 1) in 
  let should_be = Program (Seq [
    Assignment (Synth, b_zero_label, 1, b_zero);
    Assignment (Synth, a_zero_label, 1, a_zero);
    Assignment (Synth, label_ab_zero, 1, Bexpr ab_zero);
    Cond [
      (Guard get_ab_zero, 
       Seq [
       Assignment (Synth, c_length_label, 1, c_length); 
       Assignment (Synth, c_length_gt_zero_label, 1, c_length_gt_zero); 
       Assignment (Synth, fn_label, 1, fn); 
       Cond [
         (Guard (GetBoolean (Synth, Delay, c_length_gt_zero_label, 1)), 
          Return (POBoolean true)); 
         (Guard (BinBinOp (And, 
           GetBoolean (Synth, Delay, fn_label, 1), 
           Not (GetBoolean  (Synth, Delay, c_length_gt_zero_label, 1)))), 
          Return (POBoolean false)); 
         (Guard (Not (BinBinOp (Or, 
           GetBoolean (Synth, Delay, fn_label, 1), 
           GetBoolean (Synth, Delay, c_length_gt_zero_label, 1)))), 
          Return (POBoolean true))]]); 
      (Guard (Not get_ab_zero), Skip "1")]]) in 
  (* print_program is; *)
  (* print_ast is; *)
  ast_equal is should_be

let test_ast_normalize_p12 ctxt = 
  let cfg = POConfig.load_annotations_json 
    "{extRandFn : {randomness: \"rand\", unit: \"unit\"}}" in 
  let is = norm_prog cfg p12 in 
  let assign_foo_a = Assignment (Source, "foo", 1, Sexpr (POString "a")) in 
  let assign_foo_b = Assignment (Source, "foo", 2, Sexpr (POString "b")) in 
  let assign_foo_c = Assignment (Source, "foo", 3, Sexpr (POString "c")) in 
  let assign_foo_phi = 
    Assignment (Synth, "foo", 6, Phi (String, "foo", [1; 2; 3; 4; 5])) in 
  (** This is just copied from the printout. *)
  let (rand_info : rand_info) = {
    salt=(POString "abc"); 
    unit_arg="unit"; 
    unit_value=(Id "some")} in 
  let assign_abc = Assignment (Source, "abc", 1, 
    Aexpr (CustomNumber ("extRandFn", [], Some rand_info))) in 
  let should_be = Program (Seq [
    assign_abc;
    Assignment (Synth, prefix ^ "1", 1, 
      Bexpr (BinNumOp (AEquals, 
        PONumber (Oratio.ReducedRatio (1234, 1)), 
        GetNumber (Source, Random, "abc", 1)))); 
    Assignment (Synth, prefix ^ "2", 1, 
      Bexpr (BinNumOp (AEquals, 
        PONumber (Oratio.ReducedRatio (2345, 1)), 
        GetNumber (Source, Random, "abc", 1)))); 
    Assignment (Synth, prefix ^ "3", 1, 
      Bexpr (BinNumOp (AEquals, 
        PONumber (Oratio.ReducedRatio (3456, 1)), 
        GetNumber (Source, Random, "abc", 1)))); 
    Assignment (Synth, prefix ^ "4", 1, 
      Bexpr (BinNumOp (Lt, 
        GetNumber (Source, Random, "abc", 1), 
        PONumber (Oratio.ReducedRatio (5000, 1))))); 
    Cond [
      (Guard (GetBoolean (Synth, Delay, prefix ^ "1", 1)),
       assign_foo_a); 
      (Guard (BinBinOp (And, 
        GetBoolean (Synth, Delay, prefix ^ "2", 1), 
        Not (GetBoolean (Synth, Delay, prefix ^ "1", 1)))), 
       assign_foo_b); 
      (Guard (BinBinOp (And, 
        GetBoolean (Synth, Delay, prefix ^ "3", 1), 
        Not (BinBinOp (Or, 
          GetBoolean (Synth, Delay, prefix ^ "2", 1), 
          GetBoolean (Synth, Delay, prefix ^ "1", 1))))), 
       assign_foo_c); 
      (Guard (BinBinOp (And, 
        GetBoolean (Synth, Delay, prefix ^ "4", 1), 
        Not (BinBinOp (Or, 
          GetBoolean (Synth, Delay, prefix ^ "3", 1), 
          BinBinOp (Or, 
            GetBoolean (Synth, Delay, prefix ^ "2", 1), 
            GetBoolean (Synth, Delay, prefix ^ "1", 1)))))), 
       Assignment (Source, "foo", 4, Sexpr (POString "d"))); 
      (Guard (Not (BinBinOp (Or, 
        GetBoolean (Synth, Delay, prefix ^ "4", 1), 
        BinBinOp (Or, 
          GetBoolean (Synth, Delay, prefix ^ "3", 1), 
          BinBinOp (Or, 
            GetBoolean (Synth, Delay, prefix ^ "2", 1), 
            GetBoolean (Synth, Delay, prefix ^ "1", 1)))))), 
       Assignment (Source, "foo", 5, Sexpr (POString "e")))]; 
  assign_foo_phi
  ]) in 
  (* print_ast is; *)
  ast_equal is should_be

let test_uniform_choice_types ctxt = 
  let p = "foo = uniformChoice(choices=[0,1,2], unit=userid);" in 
  let is = norm_prog cfg p in 
  let should_be = Program (Assignment (Source, "foo", 1, 
    Aexpr (RandomNumber (
      POArray (Number, [
      Aexpr (PONumber (Oratio.ReducedRatio (1, 3))); 
      Aexpr (PONumber (Oratio.ReducedRatio (1, 3))); 
      Aexpr (PONumber (Oratio.ReducedRatio (1, 3)))]), 
      POArray (Number, [
      Aexpr (PONumber (Oratio.ReducedRatio (0, 1))); 
      Aexpr (PONumber (Oratio.ReducedRatio (1, 1))); 
      Aexpr (PONumber (Oratio.ReducedRatio (2, 1)))]), 
      Userid, POString "foo")))) in 
  assert_equal is should_be

let test_rewrite_guards ctxt = 
  let is = norm_prog cfg p19 in
  let choices = POArray (Number, [
    Aexpr (PONumber (Oratio.ReducedRatio (0, 1)));
    Aexpr (PONumber (Oratio.ReducedRatio (1, 1))); 
    Aexpr (PONumber (Oratio.ReducedRatio (2, 1)))]) in 
  let weights = POArray (Number, [
    Aexpr (PONumber (Oratio.ReducedRatio (1, 3))); 
    Aexpr (PONumber (Oratio.ReducedRatio (1, 3)));
    Aexpr (PONumber (Oratio.ReducedRatio (1, 3)))]) in 
  let foo = 
    Aexpr (RandomNumber (weights, choices, Userid, POString "foo")) in 
  let foo_zero = Bexpr (BinNumOp (AEquals, 
    PONumber (Oratio.ReducedRatio (0, 1)), 
    GetNumber (Source, Delay, "foo", 1))) in 
  let fvid1 = GetBoolean (Synth, Delay, "^fvid1", 1) in 
  let assign_bar_a = Assignment (Source, "bar", 1, Sexpr (POString "a")) in 
  let assign_bar_b = Assignment (Source, "bar", 2, Sexpr (POString "b")) in 
  let assign_bar_phi = 
    Assignment (Synth, "bar", 3, Phi (String, "bar", [1; 2])) in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, foo);
    Assignment (Synth, "^fvid1", 1, foo_zero); 
    Cond [
      (Guard (Not fvid1), assign_bar_a); 
      (Guard fvid1, assign_bar_b)]; 
    assign_bar_phi]) in 
  (*print_ast is;
  print_ast should_be;*)
  ast_equal is should_be

let test_inconsistent_types ctxt = 
  assert_raises 
    (Syntax.TypeError (Number, String, Phi (Unknown, "bar", [1;2])))
    (fun _ -> norm_prog cfg p20);  
  assert_raises
    (Syntax.TypeError (Number, String, Phi (Unknown, "bar", [1;2])))
    (fun _ -> norm_prog cfg p21)


let test_return_consistency1 ctxt = 
  let is = norm_prog cfg p22 in 
  let is_enabled_1 = Aexpr (PONumber (Oratio.ReducedRatio (0, 1))) in 
  let is_enabled_2 = Aexpr (PONumber (Oratio.ReducedRatio (1, 1))) in 
  let is_enabled_phi = Phi (Number, "is_enabled", [2; 1]) in 
  let some_threshold_ms_1 = Aexpr (PONumber (Oratio.ReducedRatio (1000, 1))) in 
  let some_threshold_ms_2 = Aexpr (PONumber (Oratio.ReducedRatio (0, 1))) in 
  let some_threshold_ms_phi = Phi (Number, "some_threshold_ms", [2; 1]) in 
  let in_whitelist = Bexpr (CustomBoolean ("externalRandomPredicate", [
        ("ep", Sexpr (POString "some_predicate")); 
        ("unit", Aexpr (GetNumber (ExtSource, External, "userid", 0)))
        ], None)) in 
  let get_in_whitelist_1 = GetBoolean (Source, Delay, "in_whitelist", 1) in 
  let get_is_enabled_phi = 
    Aexpr (GetNumber (Synth, Delay, "is_enabled", 3)) in 
  let in_exp_zero = Bexpr (BinNumOp (AEquals,
    PONumber Oratio.zero,
    GetNumber (Source, Delay, "in_experiment", 1))) in 
  let get_in_exp_zero = GetBoolean (Synth, Delay, "^fvid1", 1) in 
  (* Assignments *)
  let assign_is_enabled_1 = 
    Assignment (Source, "is_enabled", 1, is_enabled_1) in 
  let assign_some_threshold_1 = 
    Assignment (Source, "some_threshold_ms", 1, some_threshold_ms_1) in 
  let assign_in_whitelist_1 = 
    Assignment (Source, "in_whitelist", 1, in_whitelist) in 
  let assign_is_enabled_2 = 
    Assignment (Source, "is_enabled", 2, is_enabled_2) in 
  let assign_some_threshold_2 = 
    Assignment (Source, "some_threshold_ms", 2, some_threshold_ms_2) in 
  let assign_some_threshold_phi = 
    Assignment (Synth, "some_threshold_ms", 3, some_threshold_ms_phi) in 
  let assign_is_enabled_phi = 
    Assignment (Synth, "is_enabled", 3, is_enabled_phi) in 
  let assign_in_experiment =     
    Assignment (Source, "in_experiment", 1, get_is_enabled_phi) in 
  let assign_in_exp_zero = 
    Assignment (Synth, "^fvid1", 1, in_exp_zero) in 
  let return_in_exp_zero = Return (Not get_in_exp_zero) in 
  let should_be = Program (Seq [
    assign_is_enabled_1;
    assign_some_threshold_1;
    assign_in_whitelist_1; 
    Cond [
      (Guard get_in_whitelist_1, 
       Seq [ assign_is_enabled_2; assign_some_threshold_2]); 
      (Guard (Not get_in_whitelist_1), Skip "2")]; 
    assign_some_threshold_phi;
    assign_is_enabled_phi;
    assign_in_experiment;
    assign_in_exp_zero;
    return_in_exp_zero
  ]) in 
  (* print_program is;
  print_ast is; *)
  ast_equal is should_be

let test_return_consistency2 ctxt = 
  let is = norm_prog cfg p23 in 
  let userid_is_1234 = Bexpr (BinNumOp (AEquals, 
    PONumber (Oratio.ReducedRatio (1234, 1)), 
    GetNumber (ExtSource, External, "userid", 0))) in 
  let label_user_id_is_1234 = prefix ^ "1" in 
  let label_in_experiment_zero = prefix ^ "2" in 
  let get_userid_is_1234 = 
    GetBoolean (Synth, Delay, label_user_id_is_1234, 1) in 
  let in_experiment_zero = Bexpr (BinNumOp (AEquals,
    PONumber Oratio.zero,
    GetNumber (Synth, Delay, "in_experiment", 2))) in 
  let get_in_experiment_zero = 
    GetBoolean (Synth, Delay, label_in_experiment_zero, 1) in 
  let assign_userid_is_1234 = 
    Assignment (Synth, label_user_id_is_1234, 1, userid_is_1234) in 
  let assign_is_enabled = Assignment (Source, "is_enabled", 1, 
    Aexpr (PONumber (Oratio.ReducedRatio (1, 1)))) in 
  let assign_threshold_ms = Assignment (Source, "threshold_ms", 1, 
    Aexpr (PONumber (Oratio.ReducedRatio (10000, 1)))) in 
  let assign_in_experiment = Assignment (Source, "in_experiment", 1, 
    Aexpr (PONumber (Oratio.ReducedRatio (1, 1)))) in 
  let assign_log = Assignment (Source, "log", 1, 
    Cexpr (POArray (String, [
      Sexpr (POString "in_experiment"); 
      Sexpr (POString "is_enabled"); 
      Sexpr (POString "threshold_ms")]))) in 
  let assign_log_phi = 
    Assignment (Synth, "log", 2, Phi (Container, "log", [1; 0])) in 
  let assign_in_experiment_phi = Assignment (Synth, "in_experiment", 2, 
    Phi (Number, "in_experiment", [1; 0])) in 
  let assign_threshold_ms_phi = Assignment (Synth, "threshold_ms", 2, 
    Phi (Number, "threshold_ms", [1; 0])) in 
  let assign_is_enabled_phi = Assignment (Synth, "is_enabled", 2, 
    Phi (Number, "is_enabled", [1; 0])) in 
  let assign_in_experiment_zero = 
    Assignment (Synth, label_in_experiment_zero, 1, in_experiment_zero) in 
  let should_be = Program (Seq [
    assign_userid_is_1234; 
    Cond [
      (Guard get_userid_is_1234, 
       Seq [
         assign_is_enabled;
         assign_threshold_ms;
         assign_in_experiment;
         assign_log]);
      (Guard (Not get_userid_is_1234), Skip "3")]; 
    assign_log_phi;
    assign_in_experiment_phi;
    assign_threshold_ms_phi;
    assign_is_enabled_phi;
    assign_in_experiment_zero;
    Return (Not get_in_experiment_zero)]) in 
  (* print_ast is; *)
  (* print_program is; *)
  (* print_program should_be; *)
  ast_equal is should_be

let test_linearize_nested ctxt = 
  let is = lin_prog p26 in 
  let should_be = Program (Seq [
    (* I know this looks weird and extraneous, but compile.js parses the 
       input program to have this multiplication. Since we aren't running 
       any other program transformations, it remains. When we run normalize
       over p26, it will not include this definition, since the expression 
       (1 * b) will be minimized to b. *)
    Assignment (Synth, "^fvid1", 1, 
      Aexpr (Abinop (Product, 
        PONumber (Oratio.ReducedRatio (1, 1)), 
        GetNumber (ExtSource, External, "b", 0)))); 
    Assignment (Synth, "^fvid2", 1, 
      Aexpr (Abinop (Product, 
        PONumber (Oratio.ReducedRatio (-1, 1)), 
        GetNumber (Synth, Unclassified, "^fvid1", 1)))); 
    Assignment (Synth, "^fvid3", 1, 
      Aexpr (Abinop (Sum, 
        GetNumber (ExtSource, External, "a", 0), 
        GetNumber (Synth, Unclassified, "^fvid2", 1)))); 
    Assignment (Source, "foo1", 1, 
      Aexpr (Abinop (Sum, 
        GetNumber (Synth, Unclassified, "^fvid3", 1), 
        PONumber (Oratio.ReducedRatio (1, 1))))); 
    Assignment (Synth, "^fvid4", 1, 
      Aexpr (Abinop (Product, 
        PONumber (Oratio.ReducedRatio (1, 1)), 
        GetNumber (ExtSource, External, "b", 0)))); 
    Assignment (Synth, "^fvid5", 1, 
      Aexpr (Abinop (Product, 
        PONumber (Oratio.ReducedRatio (-1, 1)), 
        GetNumber (Synth, Unclassified, "^fvid4", 1)))); 
    Assignment (Synth, "^fvid6", 1, 
      Aexpr (Abinop (Sum, 
        GetNumber (ExtSource, External, "a", 0), 
        GetNumber (Synth, Unclassified, "^fvid5", 1)))); 
    Assignment (Source, "foo2", 1, 
      Aexpr (Abinop (Sum, 
        GetNumber (Synth, Unclassified, "^fvid6", 1), 
        PONumber (Oratio.ReducedRatio (1, 1))))); 
    Assignment (Synth, "^fvid7", 1, 
      Aexpr (Abinop (Sum, 
        GetNumber (ExtSource, External, "a", 0), 
        GetNumber (ExtSource, External, "b", 0)))); 
    Assignment (Source, "foo3", 1, 
      Aexpr (Abinop (Sum, 
        GetNumber (Synth, Unclassified, "^fvid7", 1), 
      PONumber (Oratio.ReducedRatio (1, 1))))); 
    Assignment (Synth, "^fvid8", 1, 
      Aexpr (Abinop (Product, 
        PONumber (Oratio.ReducedRatio (1, 1)), 
        GetNumber (ExtSource, External, "b", 0)))); 
    Assignment (Synth, "^fvid9", 1, 
      Aexpr (Abinop (Product, 
        PONumber (Oratio.ReducedRatio (-1, 1)), 
        GetNumber (Synth, Unclassified, "^fvid8", 1))));
    Assignment (Synth, "^fvid10", 1, 
      Aexpr (Abinop (Sum, 
        GetNumber (ExtSource, External, "a", 0), 
        GetNumber (Synth, Unclassified, "^fvid9", 1)))); 
    Assignment (Source, "foo", 1, 
      Aexpr (Abinop (Sum, 
        GetNumber (Synth, Unclassified, "^fvid10", 1), 
        PONumber (Oratio.ReducedRatio (1, 1)))))]) in 
  ast_equal is should_be

let test_map_issue ctxt = 
  let open Syntax in 
  assert_raises 
    ~msg:"Variable in_whitelist is assigned to inconsistent types."
    (TypeError (Number, Boolean, Bexpr (BinBinOp (And, Not (BinNumOp (AEquals, PONumber (Oratio.ReducedRatio (0, 1)), GetNumber (ExtSource, External, "userid", 0))), BIexpr (POMap (Number, Syntax.POMap_.empty |> POMap_.add "1234" (Aexpr (PONumber (Oratio.ReducedRatio (1, 1))))), Aexpr (GetNumber (ExtSource, External, "userid",0)))))))
    (fun _ -> norm_prog cfg p24)

let test_iexpr_specialize_type ctxt = 
  let is = norm_prog cfg p31 in 
  let assign_bar_1 = Assignment (Source, "bar", 1, Aexpr (AIexpr (
    GetContainer (ExtSource, External, "baz", 0, Number),
    Sexpr (POString "a")))) in 
  let assign_bar_2 = 
    Assignment (Source, "bar", 2, Aexpr (PONumber Oratio.one)) in 
  let assign_bar_phi = 
    Assignment (Synth, "bar", 3, Phi (Number, "bar", [1; 2])) in 
  let should_be = Program (Seq [
    Cond [(Guard (GetBoolean (ExtSource, External, "foo", 0)),
         assign_bar_1);
        (Guard (Not (GetBoolean (ExtSource, External, "foo", 0))), 
         assign_bar_2)];
    assign_bar_phi
  ]) in 
  ast_equal is should_be

let test_ext_guard_type ctxt = 
  let cfg = POConfig.load_annotations_json 
    "{ some_number : { domain : \"number\" }}" in 
  let is = norm_prog cfg p32 in 
  let fvid1s = prefix ^ "1" in 
  let assign_some_number_zero = Assignment (Synth, fvid1s, 1, 
    Bexpr (BinNumOp (AEquals, 
      PONumber Oratio.zero, 
      GetNumber (ExtSource, External, "some_number", 0)))) in 
  let fvid = GetBoolean (Synth, Delay, fvid1s, 1) in 
  let assign_foo_one = Assignment (Source, "foo", 1, 
    Aexpr (PONumber Oratio.one)) in 
  let assign_foo_zero = Assignment (Source, "foo", 2, 
    Aexpr (PONumber Oratio.zero)) in 
  let assign_foo_phi = Assignment (Synth, "foo", 3,
    Phi (Number, "foo", [1;2])) in 
  let should_be = Program (Seq [
    assign_some_number_zero;
    Cond [
      (Guard (Not fvid), assign_foo_one);
      (Guard fvid, assign_foo_zero)
    ];
    assign_foo_phi
  ]) in 
  ast_equal is should_be

let test_icse_example ctxt = 
  let cfg = POConfig.load_annotations_json "{
  deviceid : {
    card : \"high\"
  },
  userid : {
    card : \"high\"
  },
  getContext : {
    dynamic : \"tv\"
  }
}" in 
  let is = norm_prog cfg icse_example in 
  (* external gets *)
  let get_deviceid = Get (ExtSource, External, "deviceid", 0) in 
  let get_userid = Get (ExtSource, External, "userid", 0) in 
  let get_country = GetString (ExtSource, External, "country", 0) in 
  (* dynamic_policy = bernoulliTrial(p=0.3, unit=userid); *)
  let label_dynamic_policy = "dynamic_policy" in 
  let dynamic_policy = Bexpr (RandomBoolean (
    POArray (Number, [
      Aexpr (PONumber (Oratio.ReducedRatio (7, 10))); 
      Aexpr (PONumber (Oratio.ReducedRatio (3, 10)))]), 
    POArray (Boolean, [
      Bexpr (POBoolean false); 
      Bexpr (POBoolean true)]), 
    Userid, POString label_dynamic_policy)) in
  let get_dynamic_policy = 
    GetBoolean (Source, Delay, label_dynamic_policy, 1) in 
  let assign_dynamic_policy =  
    Assignment (Source, label_dynamic_policy, 1, dynamic_policy) in 
  (* context = getContext(deviceid=deviceid, userid=userid); *)
  let label_context = "context" in 
  let context = CustomExpr ("getContext", [
      ("deviceid", get_deviceid); 
      ("userid", get_userid)], 
    None) in 
  let get_context = Get (Source, Delay, label_context, 1) in 
  let assign_context = Assignment (Source, label_context, 1, context) in 
  (* weights = getBanditWeights(context=context);  *)
  let label_weights = "weights" in 
  (* note: right now we can't infer the codomain of a function whose codomain
     is a container (i.e., the inference is only one-level deep. *)
  let weights = Cexpr (CustomContainer ("getBanditWeights", [
      ("context", get_context); ("userid", get_userid)], 
    Unknown, None)) in 
  let get_weights = GetContainer (Source, Delay, label_weights, 1, Number) in 
  let assign_weights = Assignment (Source, label_weights, 1, weights) in 
  (* choices = getBanditChoices(context=context); *)
  let label_choices = "choices" in 
  let choices = Cexpr (CustomContainer ("getBanditChoices", [
    ("context", get_context); ("userid", get_userid)], 
    Number, None)) in 
  let get_choices = GetContainer (Source, Delay, label_choices, 1, Number) in 
  let assign_choices = Assignment (Source, label_choices, 1, choices) in 
  (* max_bitrate = weightedChoice(choices=choices, weights=weights,
                 unit=userid); *)
  let label_max_bitrate = "max_bitrate" in 
  let max_bitrate_1 = Aexpr (RandomNumber (get_weights, get_choices, Userid, 
  POString label_max_bitrate)) in 
  (* let get_max_bitrate_n n = 
    GetNumber (Source, Delay, label_max_bitrate, n) in  *)
  let assign_max_bitrate_1 = 
    Assignment (Source, label_max_bitrate, 1, max_bitrate_1) in 
  (* emerging_market = (country == 'IN') || (country == 'BR'); *)
  let label_country_is_brazil = prefix ^ "1" in 
  let label_country_is_india = prefix ^ "2" in 
  let label_emerging_market = "emerging_market" in 
  let get_country_is_brazil = 
    GetBoolean (Synth, Delay, label_country_is_brazil, 1) in 
  let get_country_is_india = 
    GetBoolean (Synth, Delay, label_country_is_india, 1) in 
  let get_emerging_market = 
    GetBoolean (Source, Delay, label_emerging_market, 1) in 
  let country_is_brazil = Bexpr (BinStrOp (SEquals, 
    get_country, POString "BR")) in 
  let country_is_india =  Bexpr (BinStrOp (SEquals, 
    get_country, POString "IN")) in 
  let emerging_market = Bexpr (BinBinOp (Or, 
    get_country_is_india, get_country_is_brazil)) in
  let assign_country_is_brazil = 
    Assignment (Synth, label_country_is_brazil, 1, country_is_brazil) in 
  let assign_country_is_india = 
    Assignment (Synth, label_country_is_india, 1, country_is_india) in 
  let assign_emerging_market = 
    Assignment (Source, label_emerging_market, 1, emerging_market) in 
  (* established_market = (country == 'US') || (country == 'CA'); *)
  let label_country_is_canada = prefix ^ "3" in 
  let label_country_is_us = prefix ^ "4" in 
  let label_established_market = "established_market" in 
  let get_country_is_us = 
    GetBoolean (Synth, Delay, label_country_is_us, 1) in 
  let get_country_is_canada = 
    GetBoolean (Synth, Delay, label_country_is_canada, 1) in 
  let get_established_market = 
    GetBoolean (Source, Delay, label_established_market, 1) in 
  let country_is_canada = Bexpr (BinStrOp (SEquals, 
    get_country, POString "CA")) in 
  let country_is_us = Bexpr (BinStrOp (SEquals, 
    get_country, POString "US")) in 
  let established_market = Bexpr (BinBinOp (Or,
    get_country_is_us, get_country_is_canada)) in
  let assign_country_is_canada = 
    Assignment (Synth, label_country_is_canada, 1, country_is_canada) in 
  let assign_country_is_us = 
    Assignment (Synth, label_country_is_us, 1, country_is_us) in 
  let assign_established_market = 
    Assignment (Source, label_established_market, 1, established_market) in
  (* max_bitrate = weightedChoice(choices=[400, 750],
                   weights=[0.9, 0.1], unit=userid); *)
  let max_bitrate_2 = Aexpr (RandomNumber (
    POArray (Number, [
      Aexpr (PONumber (Oratio.ReducedRatio (9, 10))); 
      Aexpr (PONumber (Oratio.ReducedRatio (1, 10)))]),
    POArray (Number, [
      Aexpr (PONumber (Oratio.ReducedRatio (400, 1))); 
      Aexpr (PONumber (Oratio.ReducedRatio (750, 1)))]), 
    Userid, POString label_max_bitrate)) in 
  let assign_max_bitrate_2 = 
    Assignment (Source, label_max_bitrate, 2, max_bitrate_2) in 
  (* max_bitrate = weightedChoice(choices=[400, 750],
                                     weights=[0.5, 0.5], unit=userid); *)
  (* let get_max_bitrate_3 = get_max_bitrate_n 3 in  *)
  let max_bitrate_3 = Aexpr (RandomNumber (
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (1, 2))); 
        Aexpr (PONumber (Oratio.ReducedRatio (1, 2)))]), 
      POArray (Number, [
        Aexpr (PONumber (Oratio.ReducedRatio (400, 1))); 
        Aexpr (PONumber (Oratio.ReducedRatio (750, 1)))]), 
      Userid, POString label_max_bitrate)) in 
  let assign_max_bitrate_3 = 
    Assignment (Source, label_max_bitrate, 3, max_bitrate_3) in
  (* max_bitrate = 400; *)
  let max_bitrate_4 = Aexpr (PONumber (Oratio.ReducedRatio (400, 1))) in 
  let assign_max_bitrate_4 = 
    Assignment (Source, label_max_bitrate, 4, max_bitrate_4) in 
  (* phis *)
  let max_bitrate_phi_1 = Phi (Number, label_max_bitrate, [2; 3; 4]) in 
  let assign_max_bitrate_phi_1 = 
    Assignment (Synth, label_max_bitrate, 5, max_bitrate_phi_1) in 
  (* let established_market_phi = 
    Phi (Boolean, label_established_market, [1; 0]) in  *)
  (* let assign_established_market_phi = 
    Assignment (Synth, label_established_market, 2, 
      established_market_phi) in  *)
  (* let emerging_market_phi = 
    Phi (Boolean, label_emerging_market, [1; 0]) in  *)
  (* let assign_emerging_market_phi = 
    Assignment (Synth, label_emerging_market, 2, emerging_market_phi) in  *)
  let max_bitrate_phi_2 = Phi (Number, label_max_bitrate, [1; 5]) in 
  let assign_max_bitrate_phi_2 =  
    Assignment (Synth, label_max_bitrate, 6, max_bitrate_phi_2) in 
  let choices_phi = Phi (Container, label_choices, [1; 0]) in 
  let assign_choices_phi = Assignment (Synth, label_choices, 2, choices_phi) in
  let weights_phi = Phi (Container, label_weights, [1; 0]) in 
  let assign_weights_phi = Assignment (Synth, label_weights, 2, weights_phi) in 
  let should_be = Program (Seq [
    assign_dynamic_policy;
    assign_context;
    assign_country_is_brazil; assign_country_is_india;
    assign_emerging_market;
    assign_country_is_canada; assign_country_is_us;
    assign_established_market;
Cond [
      (Guard get_dynamic_policy, 
       Seq [
        assign_weights; assign_choices; assign_max_bitrate_1]); 
      (Guard (Not get_dynamic_policy), 
       Seq [
        Cond [
          (Guard get_emerging_market, assign_max_bitrate_2);
          (Guard (BinBinOp (And, 
            get_established_market, Not get_emerging_market)),
           assign_max_bitrate_3); 
          (Guard (Not (BinBinOp (Or, 
            get_established_market, get_emerging_market))), 
           assign_max_bitrate_4)];
        assign_max_bitrate_phi_1])];
    (* assign_established_market_phi; assign_emerging_market_phi; *)
    assign_max_bitrate_phi_2;
    assign_choices_phi; assign_weights_phi]) in 
  (* print_program is; *)
  (* print_program should_be; *)
  ast_equal is should_be

let test_phi_nodes _ = 
    let is = norm_prog cfg phi_test in 
    let false_expr = Bexpr (POBoolean false) in 
    let true_expr = Bexpr (POBoolean true) in 
    let label_skip_logging = "skip_logging" in 
    let assign_skip_logging_1 = 
        Assignment (Source, label_skip_logging, 1, false_expr) in 
    let label_enabled = "enabled" in 
    let assign_enabled_1 = 
        Assignment (Source, label_enabled, 1, false_expr) in
    let label_ep_fn = "externalPredicate" in 
    let label_userid = "userid" in 
    let label_ep = "ep" in 
    let get_userid = 
      Aexpr (GetNumber (Config.ExtSource, External, label_userid, 0)) in 
    let ep_asdf = CustomBoolean (label_ep_fn, [
        label_userid, get_userid;
        label_ep, Sexpr (POString "asdf")
      ], None) in 
    let ep_fdsa = CustomBoolean (label_ep_fn, [
        label_userid, get_userid;
        label_ep, Sexpr (POString "fdsa")
      ], None) in 
    let assign_skip_logging_2 = 
        Assignment (Source, label_skip_logging, 2, true_expr) in 
    let label_ep_asdf = prefix ^ "3" in 
    let label_ep_fdsa = prefix ^ "2" in 
    let assign_ep_asdf = 
      Assignment (Synth, label_ep_asdf, 1, Bexpr ep_asdf) in 
    let assign_ep_fdsa = 
      Assignment (Synth, label_ep_fdsa, 1, Bexpr ep_fdsa) in 
    let get_ep_asdf = 
      GetBoolean (Synth, Delay, label_ep_asdf, 1) in 
    let get_ep_fdsa = 
      GetBoolean (Synth, Delay, label_ep_fdsa, 1) in 
    let label_launched = "launched" in 
    let launched_1 = Bexpr (RandomBoolean (
        POArray (Number, [
            Aexpr (PONumber (Oratio.ReducedRatio (1,5)));
            Aexpr (PONumber (Oratio.ReducedRatio (4,5)))
        ]),
        POArray (Boolean, [false_expr; true_expr]),
        Userid, 
        POString label_launched
      )) in 
    let assign_launched_1 = 
        Assignment (Source, label_launched, 1, launched_1) in 
    let get_launched = GetBoolean (Source, Delay, label_launched, 1) in 
    let assign_enabled_2 = 
        Assignment (Source, label_enabled, 2, true_expr) in 
    let assign_skip_logging_3 = 
        Assignment (Source, label_skip_logging, 3, true_expr) in 
    let enabled_bt = Bexpr (RandomBoolean (
        POArray (Number, [
            Aexpr (PONumber (Oratio.ReducedRatio (1,2)));
            Aexpr (PONumber (Oratio.ReducedRatio (1,2)))
        ]),
        POArray (Boolean, [false_expr; true_expr]),
        Userid, 
        POString label_enabled
      )) in 
    let assign_enabled_3 = 
        Assignment (Source, label_enabled, 3, enabled_bt) in 
    let assign_enabled_4 = Assignment (Synth, label_enabled, 4, 
        Phi (Boolean, label_enabled, [2;3])) in 
    let assign_skip_logging_4 = Assignment (Synth, label_skip_logging, 4,
        Phi (Boolean, label_skip_logging, [3;1])) in 
    let assign_skip_logging_5 = Assignment (Synth, label_skip_logging, 5, 
        Phi (Boolean, label_skip_logging, [2;4])) in 
    let get_skip_logging_5 = GetBoolean (Synth, Delay, label_skip_logging, 5) in
    let assign_enabled_5 = Assignment (Synth, label_enabled, 5,
        Phi (Boolean, label_enabled, [4;1])) in 
    let assign_launched_2 = Assignment (Synth, label_launched, 2, 
        Phi (Boolean, label_launched, [1;0])) in 
    let label_use_in_fly_out = "use_in_flyout" in 
    let assign_use_in_fly_out = Assignment (Source, label_use_in_fly_out, 1, 
        Bexpr (GetBoolean (Synth, Delay, label_enabled, 5))) in 
    let label_ep_guard = prefix ^ "1" in 
    let ep_guard = BinBinOp (Or, get_ep_asdf, Not get_ep_fdsa) in 
    let assign_ep_guard = Assignment (Synth, label_ep_guard, 1, 
        Bexpr ep_guard) in 
    let get_ep_guard = GetBoolean (Synth, Delay, label_ep_guard, 1) in 
    let should_be = Program (Seq [
        assign_skip_logging_1; assign_enabled_1;
        assign_ep_fdsa; assign_ep_asdf; 
        assign_ep_guard;
        Cond [
          (Guard get_ep_guard, assign_skip_logging_2 );
          (Guard (Not get_ep_guard), 
            Seq [
              assign_launched_1;
              Cond [
                (Guard get_launched, 
                 Seq [ assign_enabled_2; assign_skip_logging_3 ]);
                (Guard (Not get_launched), assign_enabled_3)
              ];
              assign_skip_logging_4;
              assign_enabled_4                  
          ])
        ];
        assign_enabled_5;
        assign_launched_2;
        assign_skip_logging_5;
        assign_use_in_fly_out;
        Cond [(Guard get_skip_logging_5, Return (POBoolean false));
              (Guard (Not get_skip_logging_5), Skip "1")]
    ]) in 
    (* print_program is; print_program should_be; *)
    ast_equal is should_be

let test_container_inf_type_pun _ = 
  let is = norm_prog cfg inf_test in 
  let should_be = Program (Seq [Assignment (Source, "foo", 1, Aexpr (PONumber (Oratio.ReducedRatio (-1, 1)))); Assignment (Source, "context", 1, Cexpr (CustomContainer ("someExternalFn", [("userid", Aexpr (GetNumber (ExtSource, External, "userid", 0)))], Unknown, None))); Assignment (Source, "all_configs", 1, Cexpr (POMap (Number, Syntax.POMap_.empty |> POMap_.add "a" (Aexpr (PONumber (Oratio.ReducedRatio (2, 1)))) |> POMap_.add "b" (Aexpr (PONumber (Oratio.ReducedRatio (3, 1))))))); Assignment (Synth, "^fvid1", 1, Iexpr (GetContainer (Source, Delay, "context", 1, Unknown), Sexpr (POString "asdf"))); Assignment (Source, "config", 1, Aexpr (AIexpr (POMap (Number, Syntax.POMap_.empty |> POMap_.add "a" (Aexpr (PONumber (Oratio.ReducedRatio (2, 1)))) |> POMap_.add "b" (Aexpr (PONumber (Oratio.ReducedRatio (3, 1))))), Get (Synth, Delay, "^fvid1", 1)))); Assignment (Synth, "^fvid2", 1, Bexpr (BinNumOp (AEquals, PONumber (Oratio.ReducedRatio (0, 1)), GetNumber (Source, Delay, "config", 1)))); Cond [(Guard (GetBoolean (Synth, Delay, "^fvid2", 1)), Return (POBoolean true)); (Guard (Not (GetBoolean (Synth, Delay, "^fvid2", 1))), Skip "1")]; Assignment (Source, "foo", 2, Aexpr (GetNumber (Source, Delay,"config", 1)))]) in 
  ast_equal is should_be 

let test_reset_exp ctxt = 
  let prog = make_program cfg reset_exp in 
  let (config, _) = Normalize.normalize cfg prog in 
  let open POConfig in 
  let cfg = get_config (prefix ^ "1") config in 
  assert_equal cfg.card High
  

let suite =
  "suite">:::[
    "test_tree_rewrite_all_null">::test_tree_rewrite_all_null;
    "test_tree_rewrite_null_numbers">::test_tree_rewrite_null_numbers;
    "test_cp_basic_numbers">::test_cp_basic_numbers;
    "test_cp_basic_containers">::test_cp_basic_containers;
    "test_cp_with_phi">::test_cp_with_phi;
    "test_min_prog_basic">::test_min_prog_basic;
    "test_min_fully_1">::test_min_fully_1;
    "test_min_fully_2">::test_min_fully_2;
    "test_linearize_type_unknown">::test_linearize_type_unknown;
    "test_linearize_number">::test_linearize_number; 
    "test_extract_iexprs">::test_extract_iexprs; 
    "test_extract_rels_from_guards">::test_extract_rels_from_guards; 
    "test_extract_fns_from_guards">::test_extract_fns_from_guards; 
    "test_add_default_guard">::test_add_default_guard;
    "test_lift_random_vars">::test_lift_random_vars; 
    "test_normalize_p1">::test_normalize_p1;
    "test_normalize_p2">::test_normalize_p2;
    "test_normalize_p3">::test_normalize_p3;
    "test_normalize_p4">::test_normalize_p4;
    "test_normalize_p5">::test_normalize_p5;
    "test_normalize_p5_annot">::test_normalize_p5_annot;
    "test_normalize_p6">::test_normalize_p6;
    "test_normalize_p7">::test_normalize_p7;
    "test_normalize_p8">::test_normalize_p8;
    "test_normalize_p9">::test_normalize_p9;
    "test_normalize_p10">::test_normalize_p10;
    "test_normalize_p11">::test_normalize_p11; 
    "test_external_random_var">::test_external_random_var;
    "test_ast_normalize_p12">::test_ast_normalize_p12;
    "test_rewrite_guards">::test_rewrite_guards;
    "test_uniform_choice_types">::test_uniform_choice_types;
    "test_inconsistent_types">::test_inconsistent_types;
    "test_return_consistency1">::test_return_consistency1;
    "test_return_consistency2">::test_return_consistency2;
    "test_linearize_nested">::test_linearize_nested;
    "test_map_issue">::test_map_issue;
    "test_iexpr_specialize_type">::test_iexpr_specialize_type;
    "test_ext_guard_type">::test_ext_guard_type;
    "test_phi_nodes">::test_phi_nodes;
    "test_container_inf_type_pun">::test_container_inf_type_pun;
    "test_icse_example">::test_icse_example;
    "test_reset_exp">::test_reset_exp
  ]

let () =  
  Mock_targets.PlanOut.register_printers ();
  (* Log.set_log_level Log.DEBUG;  *)
  Printf.printf "Running %s" __FILE__;
  run_test_tt_main suite