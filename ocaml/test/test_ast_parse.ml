open OUnit2
open Config 
open Programs_aux

open Mock_targets.PlanOut
open Po_syntax

let make_program = make_program2 Parse.exec_po_compiler Parse.make_program
let cfg = POConfig.load_annotations_json default_annot
let ast_equal = ast_equal assert_bool 

let p1 = "foo = 10 + bar;"
let p2 = "foo = null;"
let p3 = "phone_number = coalesce(phone_number, 0);
condition = uniformChoice(choices=[\"a\", \"b\", \"c\"], unit=phone_number);"
let p4 = "a = bernoulliTrial(p=0.3, unit=userid);
if (a) {
    return true;
}
return false;
"
let p5 = "a = 10;
b = a + 10;
if (b < 4) {
    return true;
}
"

let random_with_salt = "x = uniformChoice(choices=colors, unit=userid); # 'x' used as salt
z = uniformChoice(choices=colors, unit=userid, salt='x'); # same value as x"

let program_oratio_float = "x = 0.266221735652;"

let test_exec_po_compiler ctxt = 
    let is = Parse.exec_po_compiler p1 in 
    let should_be = "{
 \"op\": \"seq\",
 \"seq\": [
  {
   \"op\": \"set\",
   \"var\": \"foo\",
   \"value\": {
    \"op\": \"sum\",
    \"values\": [
     10,
     {
      \"op\": \"get\",
      \"var\": \"bar\"
     }
    ]
   }
  }
 ]
}
" in
    assert_equal is should_be

let test_simple_parse ctxt = 
    let is = make_program cfg p2 in
    let should_be = Program (Seq [
        Assignment (Source, "foo", 1, Null)
    ]) in 
    assert_equal is should_be

let test_external_marking ctxt = 
    let is = make_program cfg p1 in 
    let should_be = Program (Seq [
        Assignment (Source, "foo", 1, Aexpr (Abinop (
            Sum, PONumber (Oratio.ratio_of_int 10), 
                 GetNumber (ExtSource, External, "bar", 0)
        )))
    ]) in 
    assert_equal is should_be

(* We used to update this manually, but with subsequent changes to the program, 
we don't have to anymore. *)
let test_external_marking2 ctxt =
    let is = make_program cfg p3 in 
    let athird = PONumber (Oratio.ReducedRatio (1, 3)) in 
    let should_be = Program (Seq [
        Assignment (Source, "phone_number", 1, Coalesce (
            Get (ExtSource, External, "phone_number", 0),
            Aexpr (PONumber (Oratio.ratio_of_int 0))));
        Assignment (Source, "condition", 1, RandomVar (
            POArray (Number, 
                [Aexpr athird; Aexpr athird; Aexpr athird]),
            (* Order of parsing means we don't know the choice types yet. *)
            POArray (Unknown,  
                [Sexpr (POString "a"); Sexpr (POString "b"); 
                    Sexpr (POString "c")]),
            UnitR "phone_number",
            POString "condition"))
    ]) in 
    (*print_ast is;
    print_ast should_be;*)
    ast_equal is should_be

let test_branch ctxt = 
    let is = make_program cfg p4 in
    let should_be = Program (Seq [
        Assignment (Source, "a", 1, RandomVar (
            POArray (Number, 
            [Aexpr (PONumber (Oratio.ReducedRatio (7, 10)));
             Aexpr (PONumber (Oratio.ReducedRatio (3, 10)))]),
            POArray (Boolean,
            [Bexpr (POBoolean false); Bexpr (POBoolean true)]),
            Userid,
            POString "a"));
        Seq [Cond [(Guard (GetBoolean (Source, Unclassified, "a", 1)), 
                    Seq [Return (POBoolean true)])]];
        Return (POBoolean false)
    ]) in 
    (* print_ast is;
    print_ast should_be; *)
    ast_equal is should_be

let test_random_salt ctxt = 
    let is = make_program cfg random_with_salt in
    let colors = GetContainer(ExtSource, External, "colors", 0, Unknown) in
    let length_of_colors =  Length(colors) in
    let p = Abinop(Div, PONumber(Oratio.ReducedRatio(1,1)), length_of_colors) in
    let probabilities = Repeat(length_of_colors, Aexpr(p)) in
    let variable_x = RandomVar(probabilities, colors, Userid, POString "x") in
    let variable_z = RandomVar(probabilities, colors, Userid, POString "x") in
    let x =  Assignment (Source, "x", 1, variable_x) in 
    let z =  Assignment (Source, "z", 1, variable_z) in 
    let should_be = Program(Seq [x; z]) in 
    (*print_ast is;
    print_ast should_be;*)
    assert_equal is should_be

let test_oratio_float ctxt = 
    let is = make_program cfg program_oratio_float in
    let ratio = Oratio.ReducedRatio(66555433913,250000000000) in
    let variable_x = Aexpr(PONumber(ratio)) in
    let x =  Assignment (Source, "x", 1, variable_x) in 
    let should_be = Program(Seq [x]) in 
    (*print_ast is;
    print_ast should_be;*)
    assert_equal is should_be

let test_external_randomness_coersion ctxt = 
    let cfg = POConfig.load_annotations_json "{fn : {randomness : \"rand\", 
        unit : \"arg2\",
        codomain : \"boolean\"} }" in
    assert_raises (Parse.make_coersion_err "fn" ~t_from:Boolean ~t_to:Number)
        (fun () -> make_program cfg p6)

let try_catch_wrap test ctxt = 
    try test ctxt with Unix.Unix_error _ -> ()

let test_guard ctxt = 
  let is = make_program cfg p19 in 
  let assign_bar_a = Assignment (Source, "bar", 1, Sexpr (POString "a")) in 
  let assign_bar_b = Assignment (Source, "bar", 2, Sexpr (POString "b")) in 
  let assign_bar_phi = 
    Assignment (Synth, "bar", 3, Phi (Unknown, "bar", [1; 2])) in 
  let should_be = Program (Seq [
    Assignment (Source, "foo", 1, 
        RandomVar (
            POArray (Number, [
                Aexpr (PONumber (Oratio.ReducedRatio (1, 3))); 
                Aexpr (PONumber (Oratio.ReducedRatio (1, 3))); 
                Aexpr (PONumber (Oratio.ReducedRatio (1, 3)))]), 
            POArray (Unknown, [
                Aexpr (PONumber (Oratio.ReducedRatio (0, 1))); 
                Aexpr (PONumber (Oratio.ReducedRatio (1, 1))); 
                Aexpr (PONumber (Oratio.ReducedRatio (2, 1)))]), 
            Userid, POString "foo")); 
    Seq [Cond [
        (Guard (GetBoolean (Source, Unclassified, "foo", 1)), Seq [assign_bar_a]); 
        (Guard (POBoolean true), Seq [assign_bar_b])]; 
    assign_bar_phi
    ]]) in 
  (*print_ast is;*)
  assert_equal is should_be

let test_return_types ctxt = 
    let is = make_program cfg p22 in 
    let assign_is_enabled_1 = Assignment (Source, "is_enabled", 1, 
        Aexpr (PONumber (Oratio.ReducedRatio (0, 1)))) in 
    let assign_is_enabled_2 = Assignment (Source, "is_enabled", 2, 
        Aexpr (PONumber (Oratio.ReducedRatio (1, 1)))) in 
    let assign_is_enabled_phi = Assignment (Synth, "is_enabled", 3, 
        Phi (Unknown, "is_enabled", [2; 1])) in 
    let assign_some_threshold_ms_1 = Assignment (Source, "some_threshold_ms", 1, 
        Aexpr (PONumber (Oratio.ReducedRatio (1000, 1)))) in 
    let assign_some_threshold_ms_2 = Assignment (Source, "some_threshold_ms", 2, 
        Aexpr (PONumber (Oratio.ReducedRatio (0, 1)))) in 
    let assign_some_threshold_ms_phi = 
        Assignment (Synth, "some_threshold_ms", 3, 
            Phi (Unknown, "some_threshold_ms", [2; 1])) in 
    let assign_in_whitelist_1 = Assignment (Source, "in_whitelist", 1, 
        CustomExpr ("externalRandomPredicate", [
            ("ep", Sexpr (POString "some_predicate")); 
            ("unit", Get (ExtSource, External, "userid", 0))],
         None)) in 
    let should_be = Program (Seq [
        assign_is_enabled_1;
        assign_some_threshold_ms_1;
        assign_in_whitelist_1;
        Seq [
            Cond [
              (Guard (GetBoolean (Source, Unclassified, "in_whitelist", 1)),
               Seq [
                   assign_is_enabled_2; 
                   assign_some_threshold_ms_2])
            ];
            assign_some_threshold_ms_phi;
            assign_is_enabled_phi];
        Assignment (Source, "in_experiment", 1, 
            Get (Synth, Unclassified, "is_enabled", 3)); 
        Return (GetBoolean (Source, Unclassified, "in_experiment", 1))]) in 
    ast_equal is should_be

let test_scientific_notation _ = 
    let json = Yojson.Basic.from_string "{op : \"seq\", \"seq\" : [8.5113803820238e-05]}" in 
    let is = Parse.make_program POConfig.empty json in 
    let should_be = Program (Seq [
        Expr (Aexpr (PONumber 
            (Oratio.ReducedRatio (425569019101, 5000000000000000))))]) in 
    ast_equal is should_be

let test_phi_nodes _ = 
    let is = make_program cfg phi_test in 
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
    let get_userid = Get (Config.ExtSource, External, label_userid, 0) in 
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
    let label_launched = "launched" in 
    let p = Abinop (Div, PONumber (Oratio.ReducedRatio (4, 1)), 
                         PONumber (Oratio.ReducedRatio (5, 1))) in 
    let launched_1 = RandomVar (
        POArray (Number, [
            Aexpr (
              Abinop (Sum, 
                PONumber Oratio.one, 
                Abinop (Product, PONumber Oratio.neg_one, p)));
            Aexpr p
        ]),
        POArray (Boolean, [false_expr; true_expr]),
        Userid, 
        POString label_launched
      ) in 
    let assign_launched_1 = 
        Assignment (Source, label_launched, 1, launched_1) in 
    let get_launched = GetBoolean (Source, Unclassified, label_launched, 1) in 
    let assign_enabled_2 = 
        Assignment (Source, label_enabled, 2, true_expr) in 
    let assign_skip_logging_3 = 
        Assignment (Source, label_skip_logging, 3, true_expr) in 
    let enabled_bt = RandomVar (
        POArray (Number, [
            Aexpr (PONumber (Oratio.ReducedRatio (1,2)));
            Aexpr (PONumber (Oratio.ReducedRatio (1,2)))
        ]),
        POArray (Boolean, [false_expr; true_expr]),
        Userid, 
        POString label_enabled
      ) in 
    let assign_enabled_3 = 
        Assignment (Source, label_enabled, 3, enabled_bt) in 
    let assign_enabled_4 = Assignment (Synth, label_enabled, 4, 
        Phi (Unknown, label_enabled, [2;3])) in 
    let assign_skip_logging_4 = Assignment (Synth, label_skip_logging, 4,
        Phi (Unknown, label_skip_logging, [3;1])) in 
    let assign_skip_logging_5 = Assignment (Synth, label_skip_logging, 5, 
        Phi (Unknown, label_skip_logging, [2;4])) in 
    let get_skip_logging_5 = 
        GetBoolean (Synth, Unclassified, label_skip_logging, 5) in
    let assign_enabled_5 = Assignment (Synth, label_enabled, 5,
        Phi (Unknown, label_enabled, [4;1])) in 
    let assign_launched_2 = Assignment (Synth, label_launched, 2, 
        Phi (Unknown, label_launched, [1;0])) in 
    let label_use_in_fly_out = "use_in_flyout" in 
    let assign_use_in_fly_out = Assignment (Source, label_use_in_fly_out, 1, 
        Get (Synth, Unclassified, label_enabled, 5)) in 
    let should_be = Program (Seq [
        assign_skip_logging_1; assign_enabled_1;
        Seq [
            Cond [
            (Guard (BinBinOp (Or, ep_asdf, Not ep_fdsa)), 
             Seq [ assign_skip_logging_2 ]);
            (Guard (POBoolean true), 
             Seq [
                assign_launched_1;
                Seq [Cond [
                    (Guard get_launched, 
                     Seq [ assign_enabled_2; assign_skip_logging_3 ]);
                    (Guard (POBoolean true), Seq [assign_enabled_3])
                  ];
                  assign_skip_logging_4;
                  assign_enabled_4                  
                ]
             ])
            ];
            assign_enabled_5;
            assign_launched_2;
            assign_skip_logging_5;
          ];
        assign_use_in_fly_out;
        Seq [Cond [(Guard get_skip_logging_5, Seq [Return (POBoolean false)])]]
    ]) in 
    (* print_program is;
    print_ast is; *)
    ast_equal is should_be 

let test_scope _ =  
    let is = make_program cfg scope_test in 
    let label_targeted = "targeted" in 
    let assign_targeted_1 = Assignment (Source, label_targeted, 1, 
        CustomExpr ("externalPredicate", [
            ("ep", Sexpr (POString "asdf"));
            ("userid", Get (ExtSource, External, "userid", 0))], 
            None)) in  
    let label_enabled = "enabled" in 
    let assign_enabled_1 =
        Assignment (Source, label_enabled, 1, Bexpr (POBoolean false)) in 
    (* let label_score = "score" in  *)
    let assign_score_1 = 
        Assignment (Source, "score", 1, 
            Aexpr (PONumber (Oratio.ReducedRatio (0, 1)))) in 
    let label_median_score = "median_score" in 
    let assign_median_score_1 = Assignment (Source, label_median_score, 1, 
        Aexpr (Abinop (Div, PONumber (Oratio.ReducedRatio (2345, 1)), 
                            PONumber (Oratio.ReducedRatio (5432, 1))))) in 
    (* let label_untargeted = "untargeted" in *)
    let assign_untargeted_1 = Assignment (Source, "untargeted", 1, 
        RandomVar (
          POArray (Po_basetypes.Number, [
            Aexpr (Abinop (Sum, 
                PONumber (Oratio.ReducedRatio (1, 1)), 
                Abinop (Product, 
                    PONumber (Oratio.ReducedRatio (-1, 1)), 
                    Abinop (Div, 
                        PONumber (Oratio.ReducedRatio (1, 1)), 
                        PONumber (Oratio.ReducedRatio (10, 1)))))); 
            Aexpr (Abinop (Div, 
                PONumber (Oratio.ReducedRatio (1, 1)), 
                PONumber (Oratio.ReducedRatio (10, 1))))]), 
          POArray (Po_basetypes.Boolean, [
              Bexpr (POBoolean false); 
              Bexpr (POBoolean true)]), Userid, POString "untargeted")) in 
    let should_be = Program (Seq [
        assign_targeted_1;
        assign_enabled_1;
        assign_score_1;
        assign_median_score_1;
        assign_untargeted_1;
           Seq [Cond [(Guard (GetBoolean (Source, Unclassified, "untargeted", 1)), Seq [Assignment (Source, "targeted", 2, Bexpr (POBoolean false)); 
           Assignment (Source, "enabled", 2, RandomVar (POArray (Po_basetypes.Number, [Aexpr (Abinop (Sum, PONumber (Oratio.ReducedRatio (1, 1)), Abinop (Product, PONumber (Oratio.ReducedRatio (-1, 1)), Abinop(Div, PONumber (Oratio.ReducedRatio (4, 1)), PONumber (Oratio.ReducedRatio (5, 1)))))); Aexpr (Abinop (Div, PONumber (Oratio.ReducedRatio (4, 1)), PONumber (Oratio.ReducedRatio (5, 1))))]), POArray (Po_basetypes.Boolean, [Bexpr (POBoolean false); Bexpr (POBoolean true)]), Userid, POString "enabled")); Seq [Cond [(Guard (GetBoolean (Source, Unclassified, "enabled", 2)), Seq [Assignment (Source, "score", 2, Get (Source, Unclassified, "median_score", 1))])]; Assignment (Synth, "score", 3, Phi (Unknown, "score", [2; 1]))]]); (Guard (POBoolean true), Seq [Seq[Cond [(Guard (GetBoolean (Source, Unclassified, "targeted", 1)), Seq [Assignment (Source, "enabled", 3, RandomVar (POArray (Po_basetypes.Number, [Aexpr (Abinop (Sum, PONumber (Oratio.ReducedRatio (1, 1)), Abinop (Product, PONumber (Oratio.ReducedRatio (-1, 1)), Abinop (Div, PONumber (Oratio.ReducedRatio (4, 1)), PONumber (Oratio.ReducedRatio (5, 1)))))); Aexpr (Abinop (Div, PONumber (Oratio.ReducedRatio (4, 1)), PONumber (Oratio.ReducedRatio (5, 1))))]), POArray (Po_basetypes.Boolean, [Bexpr (POBoolean false); Bexpr (POBoolean true)]), Userid, POString "enabled")); Seq [Cond [(Guard (GetBoolean (Source, Unclassified, "enabled", 3)), Seq [Assignment (Source, "has_normal_score", 1, RandomVar (POArray (Po_basetypes.Number, [Aexpr (Abinop (Sum, PONumber (Oratio.ReducedRatio (1, 1)), Abinop (Product, PONumber (Oratio.ReducedRatio (-1, 1)), Abinop (Div, PONumber (Oratio.ReducedRatio (1, 1)), PONumber (Oratio.ReducedRatio (2, 1)))))); Aexpr (Abinop (Div, PONumber (Oratio.ReducedRatio (1, 1)), PONumber (Oratio.ReducedRatio (2, 1))))]), POArray (Po_basetypes.Boolean, [Bexpr (POBoolean false); Bexpr (POBoolean true)]),Userid, POString "has_normal_score")); Seq [Cond [(Guard (GetBoolean (Source, Unclassified, "has_normal_score", 1)), Seq [Assignment (Source, "score", 4, CustomExpr ("foo", [("userid", Get (ExtSource, External, "userid", 0))], None))]); (Guard (POBoolean true), Seq [Assignment (Source, "score", 5, Get (Source, Unclassified, "median_score", 1))])]; 
           Assignment (Synth, "score", 6, Phi (Unknown, "score", [4; 5]))]])]; Assignment (Synth, "score", 7, Phi (Unknown, "score", [6; 1])); 
           Assignment (Synth, "has_normal_score", 2, Phi (Unknown, "has_normal_score", [1; 0]))]]); (Guard (POBoolean true), Seq [Return (POBoolean false)])]; 
           Assignment (Synth, "score", 8, Phi (Unknown, "score", [7; 1])); Assignment (Synth, "has_normal_score", 3, Phi (Unknown, "has_normal_score", [2; 0])); 
           Assignment (Synth, "enabled", 4, Phi (Unknown, "enabled", [3; 1]))]])]; 
           Assignment (Synth, "has_normal_score", 4, Phi (Unknown, "has_normal_score", [3; 0])); 
           Assignment (Synth, "score", 9, Phi (Unknown, "score", [3; 8])); 
           Assignment (Synth, "enabled", 5, Phi (Unknown, "enabled", [2; 4])); 
           Assignment (Synth, "targeted", 3, Phi (Unknown, "targeted", [2; 1]))]]) in 
    ast_equal is should_be

let test_inf_test _ = 
    let is = make_program cfg inf_test in 
    let should_be = Program (Seq [
      Assignment (Source, "foo", 1, 
        Aexpr (Abinop (Product, 
          PONumber (Oratio.ReducedRatio (-1, 1)), 
          PONumber (Oratio.ReducedRatio (1, 1))))); 
      Assignment (Source, "context", 1, 
        CustomExpr ("someExternalFn", [
          ("userid", Get (ExtSource, External, "userid", 0))], None)); 
      Assignment (Source, "all_configs", 1, 
        Cexpr (POMap (Po_basetypes.Unknown, 
          Syntax.POMap_.empty 
          |> POMap_.add "a" (Aexpr (PONumber (Oratio.ReducedRatio (2, 1)))) 
          |> POMap_.add "b" (Aexpr (PONumber (Oratio.ReducedRatio (3, 1))))))); 
      Assignment (Source, "config", 1, 
        Iexpr (
          GetContainer (Source, Unclassified, "all_configs", 1, Unknown), 
          Iexpr (
            GetContainer (Source, Unclassified, "context", 1, Unknown), 
            Sexpr (POString "asdf")))); 
      Seq [Cond [
        (Guard (Not (GetBoolean (Source, Unclassified, "config", 1))), 
      Seq [Return (POBoolean true)])]]; 
      Assignment (Source, "foo", 2, Get (Source, Unclassified, "config", 1))]) in 
    ast_equal is should_be

let test_external_function_parse _ = 
  let cfg = POConfig.load_annotations_json 
    "{extRandFn : {randomness: \"rand\", unit: \"unit\"}}" in 
  let is = make_program cfg p12 in 
  let should_be = Program (Seq [
      Assignment (Source, "abc", 1, 
        CustomExpr ("extRandFn", [], Some {unit_arg = "unit"; unit_value = Id "some"; salt = POString ""})); 
      Seq [Cond [(Guard (BinNumOp (AEquals, PONumber (Oratio.ReducedRatio (1234, 1)), GetNumber (Source, Unclassified, "abc", 1))), Seq [Assignment (Source, "foo", 1, Sexpr (POString "a"))]); (Guard (BinNumOp (AEquals, PONumber (Oratio.ReducedRatio (2345, 1)), GetNumber (Source, Unclassified, "abc", 1))), Seq [Assignment (Source, "foo", 2, Sexpr (POString "b"))]); (Guard (BinNumOp (AEquals, PONumber (Oratio.ReducedRatio (3456, 1)), GetNumber (Source, Unclassified, "abc", 1))), Seq [Assignment (Source, "foo", 3, Sexpr (POString "c"))]); (Guard (BinNumOp (Lt, GetNumber (Source, Unclassified, "abc", 1), PONumber (Oratio.ReducedRatio (5000, 1)))), Seq [Assignment (Source, "foo", 4, Sexpr (POString "d"))]); (Guard (POBoolean true), Seq [Assignment (Source, "foo", 5, Sexpr (POString "e"))])]; Assignment (Synth, "foo", 6, Phi (Unknown, "foo", [1; 2; 3; 4; 5]))]]) in 
  ast_equal is should_be


let suite =
    "suite">:::
    [
        "test_exec_po_compiler">::test_exec_po_compiler;
        "test_simple_parse">::test_simple_parse;
        "test_external_marking">::test_external_marking;
        "test_external_marking2">::test_external_marking2;
        "test_branch">::test_branch;
        "test_random_salt">::test_random_salt;
        "test_external_randomness_coersion">::test_external_randomness_coersion;
        "test_oratio_float">::test_oratio_float;
        "test_guard">::test_guard;
        "test_return_types">::test_return_types;
        "test_scientific_notation">::test_scientific_notation;
        "test_phi_nodes">::test_phi_nodes;
        "test_scope">::test_scope;
        "test_inf_test">::test_inf_test;
        "test_external_function_parse">::test_external_function_parse
    ]

let () = 
    Printf.printf "Running %s" __FILE__;
    run_test_tt_main suite
