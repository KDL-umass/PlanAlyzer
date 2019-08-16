open OUnit2
open Config

module Targets = Mock_targets
open Targets.PlanOut.POConfig

let load_annotations = load_annotations_json

let test_empty_config ctxt = 
    let tq = load_annotations "" in
    assert_equal tq empty

let test_partial_qualifier ctxt = 
    let str = "{foo : {card : \"high\"}}" in 
    let tq = load_annotations str in 
    let cfg = get_config "foo" tq in 
    let should_be = load_annotations "" 
        |> add_default "foo"
        |> get_config "foo"
        |> update_cardinality High in 
    assert_equal cfg should_be

let test_capitalized ctxt = 
    let str = "{foo : {card : \"High\"}}" in 
    let tq = load_annotations str in 
    let cfg = get_config "foo" tq in 
    let should_be = load_annotations "" 
        |> add_default "foo"
        |> get_config "foo"
        |> update_cardinality High in 
    assert_equal cfg should_be

let test_domain ctxt =
    let open Po_basetypes in 
    let str = "{foo : {domain : \"boolean\"}}" in 
    let dom = (load_annotations str |> get_config "foo").domain in 
    let should_be = Var Boolean in 
    assert_equal dom should_be

let test_complex_domain ctxt = 
    let open Po_basetypes in
    let str = "{foo : {domain : [[\"bar\", \"boolean\"], [\"unit\", \"string\"]]}}" in 
    let dom = (load_annotations str |> get_config "foo").domain in 
    let should_be = FnArg [("bar", Boolean); ("unit", String)] in 
    assert_equal dom should_be
    
let test_bad_cardinality ctxt = 
    let str = "{foo : {card : \"hi\"}}" in 
    let hi = Sexplib.Sexp.of_string "hi" in 
    assert_raises 
        (MalformedAnnotationExpression ("foo", "cardinality", hi))
        (fun () -> load_annotations str)
    
let test_bad_dynamism ctxt = 
    let str = "{foo : {dynamism : \"timevarying\"}}" in 
    let tv = Sexplib.Sexp.of_string "timevarying" in 
    assert_raises
        (MalformedAnnotationExpression ("foo", "dynamism", tv))
        (fun () -> (load_annotations str))

let test_bad_randomness_string ctxt =
    let str = "{foo : {randomness : \"True\"}}" in 
    let rand = Sexplib.Sexp.of_string "True" in 
    assert_raises 
        (MalformedAnnotationExpression ("foo", "randomness", rand))
        (fun () -> load_annotations str)

let test_bad_randomness_int ctxt = 
    let str = "{foo : {randomness : 0}}" in 
    let rand = Sexplib.Sexp.of_string "0" in 
    assert_raises 
        (MalformedAnnotationExpression ("foo", "randomness", rand))
        (fun () -> load_annotations str)

let test_bad_randomness_float ctxt = 
    let str = "{foo : {randomness : 1.0}}" in 
    let rand = Sexplib.Sexp.of_string "1." in 
    assert_raises 
        (MalformedAnnotationExpression ("foo", "randomness", rand))
        (fun () -> load_annotations str)

let test_bad_domain_1 ctxt = 
    let str = "{foo : {domain: \"ratio\"}}" in 
    assert_raises UnsupportedDomain (fun () -> load_annotations str)
    

let suite =
    "suite">:::
    [
        "test_empty_config">:: test_empty_config;
        "test_partial_qualifier">:: test_partial_qualifier;
        "test_capitalized">:: test_capitalized;
        "test_domain">:: test_domain;
        "test_complex_domain">:: test_complex_domain;
        "test_bad_cardinality">:: test_bad_cardinality;
        "test_bad_dynamism">:: test_bad_dynamism;
        "test_bad_randomness_string">:: test_bad_randomness_string;
        "test_bad_randomness_int">:: test_bad_randomness_int;
        "test_bad_randomness_float">:: test_bad_randomness_float;
        "test_bad_domain_1">:: test_bad_domain_1
    ]

let () = 
    Printf.printf "Running %s" __FILE__;
    run_test_tt_main suite 