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

module TestGraph = Graph.Make(struct
    open Sexplib.Conv
    type key = string [@@deriving sexp]
    type program = test_program
    let key_compare = String.compare
    let key_to_str k = k  
    let get_program_variables _ = test_keys
  end)
  

(** Returns a graph with the structure:
        A 
       / \
      B   C
         / \
        D   E
 *)
let populate_graph_1 () = 
    let graph = TestGraph.initialize_adjacency_matrix test_keys in 
    let add_edge k1 k2 g = TestGraph.set g ~from_node:k1 ~to_node:k2 1 in 
    add_edge a b graph
    |> add_edge a c
    |> add_edge c d
    |> add_edge c e
    
let test_basic_set_get ctxt = 
    let g = populate_graph_1 () in 
    assert_equal (TestGraph.get g ~from_node:a ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:b) 1;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:c) 1;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:d) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:e) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:c) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:d) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:e) 0;
    assert_equal (TestGraph.get g ~from_node:c ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:c ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:c ~to_node:c) 0;
    assert_equal (TestGraph.get g ~from_node:c ~to_node:d) 1;
    assert_equal (TestGraph.get g ~from_node:c ~to_node:e) 1;
    assert_equal (TestGraph.get g ~from_node:d ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:d ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:d ~to_node:c) 0;
    assert_equal (TestGraph.get g ~from_node:d ~to_node:d) 0;
    assert_equal (TestGraph.get g ~from_node:d ~to_node:e) 0;
    assert_equal (TestGraph.get g ~from_node:e ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:e ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:e ~to_node:c) 0;
    assert_equal (TestGraph.get g ~from_node:e ~to_node:d) 0;
    assert_equal (TestGraph.get g ~from_node:e ~to_node:e) 0

let test_nodes ctxt = 
    let g = populate_graph_1 () in 
    assert_equal (TestGraph.nodes g) test_keys    

let test_edges ctxt = 
    let g = populate_graph_1 () in 
    assert_equal (TestGraph.edges g) [(a, b); (a, c); (c, d); (c, e)]

let test_remove ctxt = 
    let g = populate_graph_1 () in 
    let g' = TestGraph.remove g a in 
    assert_equal (TestGraph.nodes g') (List.tl test_keys);
    assert_equal (TestGraph.edges g') [(c, d); (c, e)]

let test_is_root ctxt = 
    let g = populate_graph_1 () in 
    assert_true (TestGraph.is_root a g);
    assert_false (TestGraph.is_root b g);
    assert_false (TestGraph.is_root c g);
    assert_false (TestGraph.is_root d g);
    assert_false (TestGraph.is_root e g)

let test_is_leaf ctxt =
    let g = populate_graph_1 () in 
    assert_false (TestGraph.is_leaf a g);
    assert_true  (TestGraph.is_leaf b g);
    assert_false (TestGraph.is_leaf c g);
    assert_true  (TestGraph.is_leaf d g);
    assert_true  (TestGraph.is_leaf e g)

let test_get_roots ctxt = 
    let g = populate_graph_1 () in 
    assert_equal (TestGraph.get_roots g) [a]

let test_get_leaves ctxt = 
    let g = populate_graph_1 () in 
    assert_equal (TestGraph.get_leaves g) [b; d; e]

let test_get_children ctxt = 
    let g = populate_graph_1 () in 
    let a_children = TestGraph.get_children g a in 
    let b_children = TestGraph.get_children g b in 
    let c_children = TestGraph.get_children g c in 
    let d_children = TestGraph.get_children g d in 
    let e_children = TestGraph.get_children g e in 
    assert_equal a_children [b; c];
    assert_equal b_children [];
    assert_equal c_children [d; e];
    assert_equal d_children [];
    assert_equal e_children []

let test_get_parents ctxt = 
    let g = populate_graph_1 () in 
    let a_parents = TestGraph.get_parents g a in 
    let b_parents = TestGraph.get_parents g b in 
    let c_parents = TestGraph.get_parents g c in 
    let d_parents = TestGraph.get_parents g d in 
    let e_parents = TestGraph.get_parents g e in 
    assert_equal a_parents [];
    assert_equal b_parents [a];
    assert_equal c_parents [a];
    assert_equal d_parents [c];
    assert_equal e_parents [c]

let test_get_ancestors ctxt = 
    let g = populate_graph_1 () in     
    let a_ancestors = TestGraph.get_ancestors g a in 
    let b_ancestors = TestGraph.get_ancestors g b in 
    let c_ancestors = TestGraph.get_ancestors g c in 
    let d_ancestors = TestGraph.get_ancestors g d in 
    let e_ancestors = TestGraph.get_ancestors g e in 
    assert_equal a_ancestors [];
    assert_equal b_ancestors [a];
    assert_equal c_ancestors [a];
    assert_equal d_ancestors [c; a];
    assert_equal e_ancestors [c; a]
    
 let test_get_descendants ctxt = 
    let g = populate_graph_1 () in 
    let a_descendants = TestGraph.get_descendants g a in 
    let b_descendants = TestGraph.get_descendants g b in 
    let c_descendants = TestGraph.get_descendants g c in 
    let d_descendants = TestGraph.get_descendants g d in 
    let e_descendants = TestGraph.get_descendants g e in 
    assert_equal a_descendants [b; c; d; e];
    assert_equal b_descendants [];
    assert_equal c_descendants [d; e];
    assert_equal d_descendants [];
    assert_equal e_descendants []

let test_collapse_node ctxt = 
    let g = populate_graph_1 () in 
    let g' = TestGraph.collapse_node c g in 
    assert_bool "Node C should have been removed."
      (TestGraph.nodes g' |> List.mem c |> not);
    assert_equal (TestGraph.get g' ~from_node:a ~to_node:b) 1;
    assert_equal (TestGraph.get g' ~from_node:a ~to_node:d) 1;
    assert_equal (TestGraph.get g' ~from_node:a ~to_node:e) 1

let test_collapse_node_2 ctxt = 
    let add_edge k1 k2 g = TestGraph.set g ~from_node:k1 ~to_node:k2 1 in 
    let y = "^Y" in 
    let fv1 = "^fvid1" in 
    let fv2 = "^fvid2" in 
    let a = "a" in 
    let b = "b" in 
    let foo = "foo" in 
    let fooid = "fooid" in 
    let g = TestGraph.initialize_adjacency_matrix 
        [y;fv1;fv2;a;b;foo;fooid] 
      |> add_edge fv1 y
      |> add_edge fv2 y
      |> add_edge a y
      |> add_edge b y
      |> add_edge foo y
      |> add_edge fooid y
      |> add_edge fv1 fv2
      |> add_edge fv2 foo
      |> add_edge a fv1
      |> add_edge b fv1
      |> add_edge fooid fv2 in 

    assert_equal (TestGraph.get g ~from_node:y ~to_node:y) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:fv1) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:fv2) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:fv1 ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:fv1 ~to_node:fv1) 0;
    assert_equal (TestGraph.get g ~from_node:fv1 ~to_node:fv2) 1;
    assert_equal (TestGraph.get g ~from_node:fv1 ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:fv1 ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:fv1 ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:fv1 ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:fv1) 0;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:fv2) 0;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:foo) 1;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:a ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:fv1) 1;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:fv2) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:b ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:fv1) 1;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:fv2) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:foo ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:fv1) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:fv2) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:fv1) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:fv2) 1;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:fooid) 0;

    let g = TestGraph.collapse_node fv1 g in 
    assert_equal (TestGraph.nodes g |> List.length) 6;

    assert_equal (TestGraph.get g ~from_node:y ~to_node:y) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:fv2) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:fv2) 0;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:foo) 1;
    assert_equal (TestGraph.get g ~from_node:fv2 ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:a ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:fv2) 1;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:b ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:fv2) 1;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:foo ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:fv2) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:fv2) 1;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:fooid) 0;

    let g = TestGraph.collapse_node fv2 g in 
    assert_equal (TestGraph.nodes g |> List.length) 5;

    assert_equal (TestGraph.get g ~from_node:y ~to_node:y) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:y ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:a ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:foo) 1;
    assert_equal (TestGraph.get g ~from_node:a ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:b ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:foo) 1;
    assert_equal (TestGraph.get g ~from_node:b ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:foo ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:foo) 0;
    assert_equal (TestGraph.get g ~from_node:foo ~to_node:fooid) 0;

    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:y) 1;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:a) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:b) 0;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:foo) 1;
    assert_equal (TestGraph.get g ~from_node:fooid ~to_node:fooid) 0


let suite =
    "suite">:::
    [ 
        "test_basic_set_get">:: test_basic_set_get;
        "test_nodes">:: test_nodes;
        "test_edges">:: test_edges;
        "test_remove">:: test_remove;
        "test_is_root">:: test_is_root;
        "test_is_leaf">:: test_is_leaf;
        "test_get_roots">:: test_get_roots;
        "test_get_children">:: test_get_children;
        "test_get_parents">:: test_get_parents;
        "test_get_ancestors">:: test_get_ancestors;
        "test_get_descendants">:: test_get_descendants;
        "test_collapse_node">:: test_collapse_node;
        "test_collapse_node_p6">::test_collapse_node_2
    ]

let () = 
    Printf.printf "Running %s" __FILE__;
    run_test_tt_main suite