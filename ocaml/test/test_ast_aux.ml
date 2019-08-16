open OUnit2

open Po_syntax
open Config 

let assert_true = assert_equal true
let assert_false = assert_equal false
let a1 = Assignment(Source, "foo", 1, 
    RandomVar (NullContainer, NullContainer, Userid, POString ""))
let a2 = Assignment(Source, "bar", 1, Null)
let a3 = Assignment(Source, "baz", 1, Null)
let a4 = Assignment (Source, "bam", 1, Null)

let program1 = Program (Seq [a1;
    Seq [a2; a3;
        Cond [(Guard (GetBoolean (Source, Delay, "foo", 1)),
               Seq [Cond [(Guard (GetBoolean (Source, Delay, "bar", 1)), 
                          Seq [])];
                    a4]);
               (Guard (GetBoolean (SrcUnknown, Delay, "asdf", 0)),
                Seq [])]
    ]
])

let test_get_node_vars ctxt = 
    let (Program p) = program1 in 
    let vars = Po_aux.get_node_vars p in 
    let should_be = Config.Params.of_list [("foo", 1); ("bar", 1); ("baz", 1); 
        ("bam", 1); ("asdf", 0)] in
    let pvars = Po_aux.get_program_vars program1 in 
    assert_equal vars should_be;
    assert_equal pvars should_be

let test_get_guard_vars ctxt = 
    let vars = Po_aux.get_guard_vars program1 in 
    let should_be = Config.Params.of_list 
        [("foo", 1); ("bar", 1); ("asdf", 0)] in
    assert_equal vars should_be

let test_get_paths_vars ctxt = 
    let assert1 = Cond [(Guard (GetBoolean (Source, Delay, "foo", 1)), 
        Skip "1")] in
    let assert2 = Cond [(Guard (GetBoolean (Source, Delay, "bar", 1)),
        Skip "2")] in
    let path = [a1; a2; a3; assert1; assert2; a4] in 
    let vars = Po_aux.get_path_vars path in 
    let should_be = Config.Params.of_list [("foo", 1); ("bar", 1); ("baz", 1); 
        ("bam", 1)] in
    assert_equal (Po_aux.get_path_vars []) Config.Params.empty;
    assert_equal (Po_aux.get_path_vars [Expr Null]) Config.Params.empty;
    assert_equal vars should_be

let test_is_var_in_program ctxt = 
    let fn = Po_aux.is_var_in_program program1 in
    assert_true (fn "foo");
    assert_true (fn "bar");
    assert_true (fn "baz");
    assert_true (fn "bam");
    assert_true (fn "asdf");
    assert_false (fn "plop")

let test_expr_external ctxt = 
    let e1 = CustomExpr ("fooFn", [], None) in 
    let cn = CustomNumber ("barFn", [], None) in 
    let e2 = Aexpr cn in 
    let e3 = Aexpr (Abinop (Sum, PONumber Oratio.one, cn)) in
    assert_equal (Po_aux.expr_external e1) (Some "fooFn");
    assert_equal (Po_aux.expr_external e2) (Some "barFn");
    assert_equal (Po_aux.expr_external e3) None

let test_get_expression_type ctxt = 
    let e1 = CustomExpr ("fooFn", [], None) in 
    let e2 = Aexpr NullNumber in 
    let e4 = Bexpr NullBoolean in 
    let e5 = Cexpr NullContainer in 
    let e6 = Sexpr NullString in 
    let e7 = Get (SrcUnknown, Delay, "foo", 0) in 
    let e8 = Iexpr (POArray (Number, [Aexpr (PONumber Oratio.one)]), 
                    Aexpr (PONumber Oratio.zero)) in 
    assert_equal (Po_aux.get_expression_type e1) Unknown;
    assert_equal (Po_aux.get_expression_type e2) Number;
    assert_equal (Po_aux.get_expression_type e4) Boolean;
    assert_equal (Po_aux.get_expression_type e5) Container; 
    assert_equal (Po_aux.get_expression_type e6) String;
    assert_equal (Po_aux.get_expression_type e7) Unknown;
    assert_equal (Po_aux.get_expression_type e8) Unknown

let test_is_bernoulli_trial ctxt = 
    let e1 = POArray(Boolean, []) in 
    let e2 = POArray(Unknown, [Bexpr (POBoolean true); 
                               Bexpr (POBoolean false)]) in 
    let e3 = POArray(Unknown, [Bexpr (POBoolean false);
                               Bexpr (POBoolean true)]) in 
    (* let e4 = POArray(Number, []) in 
    let e5 = POArray(Unknown, [Aexpr (PONumber Oratio.one);
                               Aexpr (PONumber Oratio.zero)]) in 
    let e6 = POArray(Unknown, [Aexpr (PONumber Oratio.zero);
                               Aexpr (PONumber Oratio.one)]) in 
    let e7 = POArray(Unknown, [Aexpr NullNumber; Aexpr NullNumber]) in 
    let e8 = POArray(Unknown, [Aexpr (PONumber (Oratio.add 
        Oratio.one Oratio.one)); Aexpr (PONumber (Oratio.zero))]) in  *)
    assert_false (Po_aux.is_bernoulli_trial e1);
    assert_true (Po_aux.is_bernoulli_trial e2);
    assert_true (Po_aux.is_bernoulli_trial e3);
    (* assert_false (Po_aux.is_bernoulli_trial e4);
    assert_true (Po_aux.is_bernoulli_trial e5);
    assert_true (Po_aux.is_bernoulli_trial e6);
    assert_false (Po_aux.is_bernoulli_trial e7);
    assert_false (Po_aux.is_bernoulli_trial e8) *)
    (* No longer considering numeric values as BTs. *)
    ()

let test_is_uniform_choice ctxt = 
    let e1 = POArray(Number, []) in 
    let e2 = POArray(Unknown, []) in 
    let e3 = POArray(String, []) in 
    let e4 = POArray(Number, [Aexpr (PONumber Oratio.one); 
                              Aexpr (PONumber Oratio.one)]) in 
    let e5 = POArray(Number, [Aexpr (PONumber Oratio.one);
                              Aexpr (PONumber (Oratio.Ratio (4,4)))]) in
    let e6 = POArray(Number, [Aexpr (PONumber Oratio.one);
                              Aexpr (Abinop (Product, 
                                (PONumber Oratio.one), 
                                (PONumber Oratio.one)))]) in
    assert_true (Po_aux.is_uniform_choice e1);
    assert_true (Po_aux.is_uniform_choice e2);
    assert_raises (TypeError (Number, String, (Cexpr e3)))
        (fun _ -> Po_aux.is_uniform_choice e3);
    assert_true (Po_aux.is_uniform_choice e4);
    assert_true (Po_aux.is_uniform_choice e5);
    assert_false (Po_aux.is_uniform_choice e6)

let test_get_ast_subtree ctxt = 
    let find_fn s = function 
    | Assignment(_, s', 1, _) when s' = s -> true
    | _ -> false in 
    let (Program p) = program1 in 
    let subtree = Po_aux.get_ast_subtree ~find_fn:(find_fn "baz") p in 
    let should_be = Seq [Seq [a3; 
    Cond [(Guard (GetBoolean (Source, Delay, "foo", 1)),
           Seq [Cond [(Guard (GetBoolean (Source, Delay, "bar", 1)), Seq [])];
                a4]);
          (Guard (GetBoolean (SrcUnknown, Delay, "asdf", 0)),
            Seq [])]]] in 
    (* We haven't set up testing for equivalent programs yet. *)
    assert_equal subtree (Some should_be);
    assert_equal (Po_aux.get_ast_subtree ~find_fn:(find_fn "plop") p) None

let test_get_all_assignments ctxt = 
    ()

let test_is_constant ctxt = 
    ()

let suite =
    "suite">:::
    [ 
        "test_get_node_vars">:: test_get_node_vars;
        "test_get_guard_vars">:: test_get_guard_vars;
        "test_get_paths_vars">:: test_get_paths_vars;
        "test_is_var_in_program">:: test_is_var_in_program;
        "test_expr_external">:: test_expr_external;
        "test_get_expression_type">:: test_get_expression_type;
        "test_is_bernoulli_trial">:: test_is_bernoulli_trial;
        "test_is_uniform_choice">:: test_is_uniform_choice;
        "test_get_ast_subtree">:: test_get_ast_subtree
    ]

let () = 
    Printf.printf "Running %s" __FILE__;
    run_test_tt_main suite