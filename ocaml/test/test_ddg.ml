open OUnit2

type test_program = TestProgram 

let a = "A"
let b = "B"
let c = "C"
let d = "D"
let e = "E"

let test_keys = [a;b;c;d;e]

let assert_true = assert_equal true 
let assert_false = assert_equal false 


module TestGraph = Ddg.Make(struct 
        open Sexplib.Conv
        type key = string [@@deriving sexp]
        type program = test_program
        let key_compare = String.compare
        let key_to_str k = k  
        let get_program_variables _ = test_keys
        let find_dependents _ = function 
        | "A" -> [b; c]
        | "B" -> []
        | "C" -> [d; e]
        | "D" -> []
        | "E" -> []
        | _ -> assert false
    end)

(** Returns a graph with the structure:
        A 
       / \
      B   C
         / \
        D   E
    This could have a corresponding example program of:
    A = bernoulliTrial(...);
    B = [0.6, 0.5][A];
    if (A) {
        C = bernoulliTrial(...);
        if (C) {
            D = ...
            E = ...
        }
    } 
 *)
let populate_graph_1 () = 
    let graph = TestGraph.initialize_adjacency_matrix test_keys in 
    let add_edge k1 k2 g = TestGraph.set g ~from_node:k1 ~to_node:k2 1 in 
    add_edge a b graph
    |> add_edge a c
    |> add_edge c d
    |> add_edge c e

(** The only additional function on top of the base graph ones is 
build_dependence_graph *)

let test_build_dependence_graph ctxt = 
    let is = TestGraph.build_dependence_graph TestProgram in 
    let should_be = populate_graph_1 () in 
    assert_equal (TestGraph.get is ~from_node:a ~to_node:a) 0;
    assert_equal (TestGraph.get is ~from_node:a ~to_node:b) 1;
    assert_equal (TestGraph.get is ~from_node:a ~to_node:c) 1;
    assert_equal (TestGraph.get is ~from_node:a ~to_node:d) 0;
    assert_equal (TestGraph.get is ~from_node:a ~to_node:e) 0;
    assert_equal (TestGraph.get is ~from_node:b ~to_node:a) 0;
    assert_equal (TestGraph.get is ~from_node:b ~to_node:b) 0;
    assert_equal (TestGraph.get is ~from_node:b ~to_node:c) 0;
    assert_equal (TestGraph.get is ~from_node:b ~to_node:d) 0;
    assert_equal (TestGraph.get is ~from_node:b ~to_node:e) 0;
    assert_equal (TestGraph.get is ~from_node:c ~to_node:a) 0;
    assert_equal (TestGraph.get is ~from_node:c ~to_node:b) 0;
    assert_equal (TestGraph.get is ~from_node:c ~to_node:c) 0;
    assert_equal (TestGraph.get is ~from_node:c ~to_node:d) 1;
    assert_equal (TestGraph.get is ~from_node:c ~to_node:e) 1;
    assert_equal (TestGraph.get is ~from_node:d ~to_node:a) 0;
    assert_equal (TestGraph.get is ~from_node:d ~to_node:b) 0;
    assert_equal (TestGraph.get is ~from_node:d ~to_node:c) 0;
    assert_equal (TestGraph.get is ~from_node:d ~to_node:d) 0;
    assert_equal (TestGraph.get is ~from_node:d ~to_node:e) 0;
    assert_equal (TestGraph.get is ~from_node:e ~to_node:a) 0;
    assert_equal (TestGraph.get is ~from_node:e ~to_node:b) 0;
    assert_equal (TestGraph.get is ~from_node:e ~to_node:c) 0;
    assert_equal (TestGraph.get is ~from_node:e ~to_node:d) 0;
    assert_equal (TestGraph.get is ~from_node:e ~to_node:e) 0;
    assert_equal is should_be

let test_po_ddg ctxt = 
    let open Programs_aux in 

  let open Mock_targets.PlanOut in 
  let make_program = make_program2 Parse.exec_po_compiler Parse.make_program in 
  let cfg = POConfig.load_annotations_json default_annot in 
  
  let prog = make_program cfg reset_exp in 
  let ddg_input = DDG.build_dependence_graph prog in 
  assert_equal (List.length (DDG.nodes ddg_input)) 1;

  let normed_prog = snd (Normalize.normalize cfg prog) in 
  let ddg_normed = DDG.build_dependence_graph normed_prog in  

  assert_equal (DDG.get ddg_normed ~to_node:("userid", 0) 
                                   ~from_node:(prefix ^ "1", 1))
                0;
  assert_equal (DDG.get ddg_normed ~from_node:("userid", 0) 
                                   ~to_node:(prefix ^ "1", 1))
                1

let suite = 
    "suite">:::[
        "test_build_dependence_graph">:: test_build_dependence_graph;
        "test_po_ddg">::test_po_ddg
    ]

let () =
    Printf.printf "Running %s" __FILE__;
    run_test_tt_main suite