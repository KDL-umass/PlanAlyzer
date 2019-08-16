open OUnit2
open Programs_aux
open Config

open Mock_targets.PlanOut

let outcome_var = "^Y"
let make_program = make_program2 Parse.exec_po_compiler Parse.make_program 
let cfg = POConfig.load_annotations_json default_annot

let transform_program cfg p =
  let p = make_program cfg p in 
  let (cfg, prog) = Normalize.normalize cfg p in 
  Transform.transform (Ast.PODdg.build_dependence_graph prog) cfg prog

let is_synthetic_variable k = 
  Core_kernel.String.is_prefix k ~prefix:Po_counters.pseudo_prefix

let remove_synthetic_variables g =
  let to_remove = CGM.nodes g |> List.filter is_synthetic_variable in 
  List.fold_left (fun g k -> CGM.collapse_node k g) g to_remove

let make_causal_graph cfg p = 
  CGM.build_causal_graphs (transform_program cfg p)
  |> List.map remove_synthetic_variables

let make_data_dependence_graph cfg p = 
  DDG.build_dependence_graph (make_program cfg p)

let test_not_experiment ctxt = 
  let ddg = make_data_dependence_graph cfg p1 in 
  let cgm = make_causal_graph cfg p1 in 
  assert_equal (List.length cgm) 1;
  let g1 = List.hd cgm in 
  let cgm_nodes = CGM.nodes g1 in 
  let ddg_nodes = DDG.nodes ddg in 
  let cgm_nodes_str = Utils.join "; " Utils.identity cgm_nodes in 
  let ddg_nodes_str = Utils.join "; " (fun (s, i) -> Printf.sprintf "%s_%d" s i) ddg_nodes in 
  (* The causal model should only have the outcome. *)
  (*Printf.printf "Graph:\n%s\n" (CGM.string_of_graph g1);*)
  assert_equal (List.length cgm_nodes) 1;
  assert_bool 
    (Printf.sprintf "%s should be in [%s]" outcome_var cgm_nodes_str)
    (List.mem outcome_var cgm_nodes);
  assert_equal (CGM.get g1 ~from_node:outcome_var ~to_node:outcome_var) 0;
  
  (* The data dependence graph should have "foo", "bar", and "baz." *)
  assert_equal (DDG.nodes ddg |> List.length) 3;
  assert_bool 
    (Printf.sprintf "(\"foo\", 1) should be in [%s]" ddg_nodes_str)
    (List.mem ("foo", 1) ddg_nodes);
  assert_bool 
    (Printf.sprintf "(\"bar\", 1) should be in [%s]" ddg_nodes_str)
    (List.mem ("bar", 1) ddg_nodes);
  assert_bool 
    (Printf.sprintf "(\"baz\", 1) should be in [%s]" ddg_nodes_str)
    (List.mem ("baz", 1) ddg_nodes);
  
  assert_equal (DDG.get ddg ~from_node:("foo", 1) ~to_node:("foo", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("foo", 1) ~to_node:("bar", 1)) 1;
  assert_equal (DDG.get ddg ~from_node:("foo", 1) ~to_node:("baz", 1)) 0;

  assert_equal (DDG.get ddg ~from_node:("bar", 1) ~to_node:("foo", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("bar", 1) ~to_node:("bar", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("bar", 1) ~to_node:("baz", 1)) 0;

  assert_equal (DDG.get ddg ~from_node:("baz", 1) ~to_node:("foo", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("baz", 1) ~to_node:("bar", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("baz", 1) ~to_node:("baz", 1)) 0

let test_basic_experiment ctxt = 
  let ddg = make_data_dependence_graph cfg p2 in 
  let cgm = make_causal_graph cfg p2 in 
  assert_equal (List.length cgm) 1;
  let g1 = List.hd cgm in 
  (*Printf.printf "%s\n" (CGM.string_of_graph g1);
  Printf.printf "%s\n" (DDG.string_of_graph ddg);*)
  let cgm_nodes = CGM.nodes g1 in 
  let cgm_nodes_str = Utils.join "; " Utils.identity cgm_nodes in 
  (* The causal model should have one cause and the outcome. *)
  assert_equal (List.length cgm_nodes) 2;
  assert_bool 
    (Printf.sprintf "%s should be in [%s]" outcome_var cgm_nodes_str)
    (List.mem outcome_var cgm_nodes);
  assert_bool 
    (Printf.sprintf "%s should be in [%s]" "foo" cgm_nodes_str)
    (List.mem outcome_var cgm_nodes);
  assert_equal (CGM.get g1 ~from_node:outcome_var ~to_node:"foo")       0;
  assert_equal (CGM.get g1 ~from_node:outcome_var ~to_node:outcome_var) 0;
  assert_equal (CGM.get g1 ~from_node:"foo" ~to_node:"foo")             0;
  assert_equal (CGM.get g1 ~from_node:"foo" ~to_node:outcome_var)       1;

  (* The data dependence graph should have weights, choices, and foo. *)
  assert_equal (DDG.nodes ddg |> List.length) 3;
  assert_equal (DDG.get ddg ~from_node:("weights", 1) ~to_node:("weights", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("choices", 1) ~to_node:("choices", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("foo", 1) ~to_node:("foo", 1))         0;
  assert_equal (DDG.get ddg ~from_node:("weights", 1) ~to_node:("choices", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("weights", 1) ~to_node:("foo", 1))     1;
  assert_equal (DDG.get ddg ~from_node:("choices", 1) ~to_node:("weights", 1)) 0;
  assert_equal (DDG.get ddg ~from_node:("choices", 1) ~to_node:("foo", 1))     1;
  assert_equal (DDG.get ddg ~from_node:("foo", 1) ~to_node:("weights", 1))     0;
  assert_equal (DDG.get ddg ~from_node:("foo", 1) ~to_node:("choices", 1))     0

let test_basic_external_random_var ctxt = 
  let cfg = POConfig.load_annotations_json
    "{fn : {randomness : \"rand\", unit : \"arg2\"}}" in 
  let cgm = make_causal_graph cfg p6 in 
  assert_equal (List.length cgm) 1;
  let g1 = List.hd cgm in 
  let cgm_nodes = CGM.nodes g1 in 
  let cgm_nodes_str = Utils.join "; " Utils.identity cgm_nodes in 
  assert_equal (CGM.nodes g1 |> List.length) 4;
  assert_bool 
    (Printf.sprintf "%s should be in [%s]" outcome_var cgm_nodes_str)
    (List.mem outcome_var cgm_nodes);
  assert_bool 
    (Printf.sprintf "%s should be in [%s]" "a" cgm_nodes_str)
    (List.mem outcome_var cgm_nodes);
  assert_bool 
    (Printf.sprintf "%s should be in [%s]" "b" cgm_nodes_str)
    (List.mem outcome_var cgm_nodes);
  assert_bool 
    (Printf.sprintf "%s should be in [%s]" "foo" cgm_nodes_str)
    (List.mem outcome_var cgm_nodes);
  assert_equal (CGM.get g1 ~from_node:outcome_var ~to_node:outcome_var) 0;
  assert_equal (CGM.get g1 ~from_node:outcome_var ~to_node:"a")         0;
  assert_equal (CGM.get g1 ~from_node:outcome_var ~to_node:"b")         0;
  assert_equal (CGM.get g1 ~from_node:outcome_var ~to_node:"foo")       0;
  assert_equal (CGM.get g1 ~from_node:"a" ~to_node:outcome_var)         1;
  assert_equal (CGM.get g1 ~from_node:"a" ~to_node:"a")                 0;
  assert_equal (CGM.get g1 ~from_node:"a" ~to_node:"b")                 0;
  assert_equal (CGM.get g1 ~from_node:"a" ~to_node:"foo")               1;
  assert_equal (CGM.get g1 ~from_node:"b" ~to_node:outcome_var)         1;
  assert_equal (CGM.get g1 ~from_node:"b" ~to_node:"a")                 0;
  assert_equal (CGM.get g1 ~from_node:"b" ~to_node:"b")                 0;
  assert_equal (CGM.get g1 ~from_node:"b" ~to_node:"foo")               1;
  assert_equal (CGM.get g1 ~from_node:"foo" ~to_node:outcome_var)       1;
  assert_equal (CGM.get g1 ~from_node:"foo" ~to_node:"a")               0;
  assert_equal (CGM.get g1 ~from_node:"foo" ~to_node:"b")               0;
  assert_equal (CGM.get g1 ~from_node:"foo" ~to_node:"foo")             0
  

let suite = 
  "suite">:::[
    "test_not_experiment">::test_not_experiment;
    "test_basic_experiment">::test_basic_experiment;
    "test_basic_external_random_var">::test_basic_external_random_var
  ]

let () =
  Printf.printf "Running %s" __FILE__;
  run_test_tt_main suite