open OUnit2
open Programs_aux
open Config 

module Mock = Mock_targets.PlanOut

let make_program = make_program2 Mock.Parse.exec_po_compiler Mock.Parse.make_program
let cfg = Mock.POConfig.load_annotations_json default_annot

module PO = Syntax
module CPO = Mock.POCorepo
module BT = Mock.Basetypes
let default_quals = {CPO.card=Low; CPO.dyn=Const; CPO.rand=Det; CPO.corr=Exo}
let make_quals ?(card=Low) ?(dyn=Const) ?(rand=Det) ?(corr=Exo) _ = 
    CPO.make_qualifiers ~card ~dyn ~rand ~corr
let default_decl = make_quals ~corr:End ()


let print_cpo_sem p = 
    CPO.Format.string_of_semantics_tuples p 
    |> Printf.printf "\n----------------------------------------\n%s
       \n----------------------------------------\n"

let print_cpo_sem_ast p = 
    ""

let print_cpoprog p =
  CPO.Format.string_of_program p
  |> Printf.printf "%s\n"
  
let transform_program cfg p = 
  let (cfg, prog) = make_program cfg p |> Mock.Normalize.normalize cfg in 
  Mock.Transform.transform (Ast.PODdg.build_dependence_graph prog) cfg prog

let eval_cpo_prog cfg p : CPO.semantic_tuple list = 
  let (cfg, prog) = make_program cfg p |> Mock.Normalize.normalize cfg in 
  let ddg = Ast.PODdg.build_dependence_graph prog in
  let transformed = 
    Mock.Transform.transform (Ast.PODdg.build_dependence_graph prog) cfg prog in
  Mock.Transform.Corepo.eval cfg ddg transformed

let rec paths_equal p_is p_should_be : unit = 
  let open Printf in 
  match p_is, p_should_be with 
  | [], [] -> ()
  | [], p | p, [] -> 
    assert_bool 
      (sprintf "Paths unequal; excess nodes: %s" 
        (CPO.Format.string_of_path p))
      true 
  | h1::t1, h2::t2 ->
    assert_bool 
      (sprintf "Paths unequal at nodes (%s, %s)"
        (CPO.Format.string_of_node h1)
        (CPO.Format.string_of_node h2))
      (h1 = h2);
    paths_equal t1 t2     

let semantics_equal (tupes_are : CPO.semantic_tuple list) 
                    (tupes_should_be : CPO.semantic_tuple list) : unit =
  let num_tupes_are = List.length tupes_are in 
  let num_tupes_should_be = List.length tupes_should_be in 
  let cond_sets_are = List.map snd tupes_are in 
  let cond_sets_should_be = List.map snd tupes_should_be in 
  let equiv_cond_set (yes_s, yes_p) (maybe_s, maybe_p) = 
    (CPO.Sigma.cardinal yes_s = CPO.Sigma.cardinal maybe_s) &&
    (CPO.Sigma.equal (=) yes_s maybe_s) &&
    (CPO.Phi.cardinal yes_p = CPO.Phi.cardinal maybe_p) &&
    (CPO.Phi.equal yes_p maybe_p) in 
  if num_tupes_are > num_tupes_should_be
  then (* We have an extra conditioning set somewhere *)
    for i=0 to List.length cond_sets_are - 1 do
      (* Check to see if this is the one that is not in cond_sets_should_be -- 
         i.e., The extra conditioning set in the output. *)
      let this = List.nth cond_sets_are i in 
      (* Try to find this conditioning set. *)
      let found = List.filter (equiv_cond_set this) cond_sets_should_be in 
      assert_bool 
          (Printf.sprintf "Unexpected cond set: %s\n%s\n for treatments %s" 
            (CPO.Format.string_of_cond_set this)
            (CPO.Format.ast_string_of_cond_set this)
            (Utils.join "\n     ===     \n" CPO.Format.string_of_treatment
              (List.nth tupes_are i |> fst))
            )
          (List.length found = 1)
    done
  else if num_tupes_are < num_tupes_should_be (*  *)
  then 
    for i=0 to List.length cond_sets_should_be - 1 do
      let this = List.nth cond_sets_should_be i in 
      assert_bool
        (Printf.sprintf "Missing cond set: %s"
          (CPO.Format.string_of_cond_set this))
        (List.filter (equiv_cond_set this) cond_sets_are 
         |> List.length |> (<>) 0)
    done
  else begin (* Check that the cond sets are equivalent and that the treatments 
    are equivalent *)
    for i=0 to List.length tupes_are - 1 do
      let (is_dtlist, is_cond_set) = List.nth tupes_are i in 
      (* First try to find the matching dtlist and conditioning set. *)
      assert_bool
        (Printf.sprintf "Unexpected conditioning set: %s\n\n%s" 
          (CPO.Format.string_of_cond_set is_cond_set)
          (CPO.Format.ast_string_of_cond_set is_cond_set))
        (List.exists (equiv_cond_set is_cond_set) cond_sets_should_be); 
      let sb_dtlist = 
        tupes_should_be
        |> List.find (fun (_, (cs, phi)) -> 
          let (cs', phi') = is_cond_set in 
          CPO.Sigma.equal (=) cs cs' && CPO.Phi.equal phi phi')
        |> fst in 
      let is_num_dtlist = List.length is_dtlist in 
      let sb_num_dtlist = List.length sb_dtlist in 
      let equiv_dt_r (yes_dt, yes_r, yes_phi) (maybe_dt, maybe_r, maybe_phi) = 
        Oratio.equals yes_r maybe_r &&
        CPO.Delta.cardinal yes_dt = CPO.Delta.cardinal maybe_dt &&
        CPO.Delta.equal (=) yes_dt maybe_dt &&
        CPO.Phi.equal yes_phi maybe_phi in 
      if is_num_dtlist > sb_num_dtlist
      then (* We have an extra treatment somewhere *)
        for i=0 to List.length is_dtlist - 1 do
            let dt_r = List.nth is_dtlist i in 
            (* Find the matching treatment. *)
            assert_bool 
                (Printf.sprintf "Extra treatment: %s"
                  (CPO.Format.string_of_treatment dt_r))
                (List.filter (equiv_dt_r dt_r) sb_dtlist 
                  |> List.length |> (<>) 0)
        done 
      else if is_num_dtlist < sb_num_dtlist
      then 
        for i=0 to List.length sb_dtlist - 1 do
            let dt_r = List.nth sb_dtlist i in 
            assert_bool 
              (Printf.sprintf "Missing treatment: %s" 
                (CPO.Format.string_of_treatment dt_r))
              (List.filter (equiv_dt_r dt_r) is_dtlist |> List.length |> (<>) 0)
        done 
      else 
        for i=0 to List.length is_dtlist - 1 do
          let (is_dt, is_r, is_dt_phi) = List.nth is_dtlist i in 
          let is_delta = Printf.sprintf "Delta:%s\n===\n" (Utils.join "; " 
            Po_format.ast_string_of_expr
            (CPO.Delta.bindings is_dt |> List.map snd)) in
          let is_phi = Printf.sprintf "Phi:%s\n\n" (Utils.join "; " 
            Po_format.ast_string_of_expr
            (CPO.Phi.elements is_dt_phi)) in
          (* Get the keys of the actual treatment environment. *)
          let is_dt_keys = CPO.Delta.bindings is_dt |> List.map fst in 
          let module KeySet = Set.Make(String) in 
          assert_bool 
            "Should be list of keys cannot be empty"
            (List.length sb_dtlist > 0);
          assert_bool 
            "Contains an empty treatment environment."
            (List.map Utils.fst3 sb_dtlist
             |> List.map CPO.Delta.cardinal
             |> List.for_all ((<>) 0));
          let dt_tupe_matched_on_dt_keys = sb_dtlist 
            |> List.filter (fun (d, _, _) -> 
                (* let sb_dt_keys = CPO.Delta.bindings d |> List.map fst in  *)
                CPO.Delta.equal (fun a b -> compare a b = 0) d is_dt)
                (* Printf.printf 
                  "ASDF: [%s] vs. [%s]\n" 
                  (Utils.join ", " Utils.identity sb_dt_keys)
                  (Utils.join ", " Utils.identity is_dt_keys);
                KeySet.equal (KeySet.of_list is_dt_keys) 
                             (KeySet.of_list sb_dt_keys))  *)
                             in
          assert_bool 
            (Printf.sprintf 
              "Unexpected treatment set with keys: [%s]."
              (Utils.join ", " Utils.identity is_dt_keys))
            (List.length dt_tupe_matched_on_dt_keys > 0);         
          if List.length dt_tupe_matched_on_dt_keys = 1 
          then begin 
            let (sb_dt, sb_r, sb_dt_phi) = List.hd dt_tupe_matched_on_dt_keys in 
            let sb_delta = Printf.sprintf "Delta:%s\n===\n" (Utils.join "; " 
              Po_format.ast_string_of_expr 
              (CPO.Delta.bindings sb_dt |> List.map snd)) in
            let sb_phi = Printf.sprintf "Phi:%s\n\n" (Utils.join "; " 
              Po_format.ast_string_of_expr
              (CPO.Phi.elements sb_dt_phi)) in
            assert_bool 
              (Printf.sprintf "Treatments not equal: %s\n\tvs.\n%s"
                is_delta sb_delta)
              (CPO.Delta.equal (=) is_dt sb_dt);
            assert_bool 
              (Printf.sprintf "Probabilities not equal: %s vs. %s"
                (Oratio.string_of_ratio is_r) 
                (Oratio.string_of_ratio sb_r))
              (Oratio.equals is_r sb_r);
            assert_bool 
              (Printf.sprintf "Unevaled treatments not equal:\n%s\n\tvs.\n%s"
                is_phi sb_phi)
              (CPO.Phi.equal is_dt_phi sb_dt_phi)
            end 
          else assert false 
        done
    done end 


let test_logging ctxt = 
  let p = "if (foo) { if (bar) { return true; } else {return false; } }" in 
  let prog = transform_program cfg p in 
  assert_equal (List.length prog) 3;
  assert_equal (List.nth prog 0 |> CPO.is_path_logged) true;
  assert_equal (List.nth prog 1 |> CPO.is_path_logged) false;
  assert_equal (List.nth prog 2 |> CPO.is_path_logged) true
  

let test_semantics_no_paths ctxt = 
  assert_raises Mock.StaticErrors.NotAnExperiment
    (fun () -> eval_cpo_prog cfg p1)

let test_basic_experiment ctxt = 
  let cfg = Mock.POConfig.load_annotations_json 
    "{userid : { card : \"high\"}}" in 
  let is = eval_cpo_prog cfg p2 in 
  (* weights and choices will need to be removed later. *)
  let weights = PO.Cexpr (PO.POArray (BT.Number, [
    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (10, 1)));
    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (2, 5)))])) in 
  let choices = PO.Cexpr (PO.POArray (BT.Unknown, [
    PO.Sexpr (PO.POString "asdf");
    PO.Bexpr (PO.POBoolean true)])) in 
  let d1 = CPO.Delta.add "foo" 
            (PO.Sexpr (PO.POString "asdf")) CPO.Delta.empty
           |> CPO.Delta.add "weights" weights
           |> CPO.Delta.add "choices" choices 
           in 
  let d2 = CPO.Delta.add "foo" 
            (PO.Bexpr (PO.POBoolean true)) CPO.Delta.empty 
           |> CPO.Delta.add "weights" weights
           |> CPO.Delta.add "choices" choices 
           in 
  let open PO in 
  let should_be = [
    ([(d1, Oratio.ReducedRatio (25, 26), CPO.Phi.empty); 
      (d2, Oratio.ReducedRatio (1, 26), CPO.Phi.empty)], 
      (CPO.Sigma.empty
       (* Remove these later. *)
       (* |> Sigma.add "choices" choices
       |> Sigma.add "weights" weights *)
      , CPO.Phi.empty))
  ] in 
  (* print_cpo_sem is; *)
  semantics_equal is should_be

let test_logged_path_no_randomization_1 ctxt = 
  let logged_path = [
      CPO.Declare (("asdf", 0), 
        make_quals ~corr:End (), Some Smtlib.bool_sort);
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
    ] in 
  assert_raises 
    (Mock.StaticErrors.LoggedPathNoRandomization logged_path)
    (fun () -> 
      eval_cpo_prog cfg p3)
    
let test_guard_always_false ctxt = 
  assert_raises Mock.StaticErrors.GuardAlwaysTrue
    (fun () -> eval_cpo_prog cfg p4)

let test_reset_exp ctxt = 
  ignore (eval_cpo_prog cfg reset_exp)

let test_external_randomness ctxt = 
    let cfg = Mock.POConfig.load_annotations_json 
      "{fn : {randomness : \"rand\", unit: \"arg1\"}}" in  
    let open PO in 
    let open BT in 
    (* Unclassified because it fails before we propagate the randomness label *)
    let unitr = (Iexpr (GetContainer (ExtSource, External, "a", 0, Unknown), 
                        Get (ExtSource, External, "b", 0))) in  
    assert_raises 
      (Mock.Parse.Malformed_unit unitr)
      (fun () -> eval_cpo_prog cfg p5) 

let test_external_randomness_downstream ctxt = 
    let cfg = Mock.POConfig.load_annotations_json 
      "{fn : {randomness : \"rand\", 
        codomain : \"number\", \"unit\" : \"arg2\"}, fooid : {card : \"high\"} }" in
    let is = eval_cpo_prog cfg p6 in
    (* Empty set returned because we have insufficient information to 
       determine any contrasts. *) 
    semantics_equal is []

let sanity_check_p7 ctxt = 
  let open BT in 
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
  let decl_quals = make_quals ~corr:End () in 
  let path_no_randomization = [
        CPO.Declare (("a", 0), decl_quals, None);
        CPO.Declare (("b", 0), decl_quals, Some Smtlib.int_sort);
        CPO.Declare (("c", 0), decl_quals, None);
        CPO.Declare (("d", 0), decl_quals, None);
        CPO.Assign (Synth, (label_a_length, 1), decl_quals, a_length);
        CPO.Assign (Synth, (label_b_mod_a_length, 1), decl_quals, b_mod_length_a);
        CPO.Assign (Synth, (label_1st_lookup, 1), decl_quals, first_lookup);
        CPO.Assign (Synth, (label_2nd_lookup, 1), decl_quals, second_lookup);
        CPO.Assign (Source, ("foo", 1), decl_quals, third_lookup);
        CPO.Return CPO.True
    ] in 
  assert_raises (Mock.StaticErrors.LoggedPathNoRandomization path_no_randomization)
    (fun () -> eval_cpo_prog cfg p7) 

let sanity_check_p8 ctxt = 
  let decl_quals = make_quals ~corr:End () in   
  let path_no_randomization = [
    CPO.Declare (("a", 0),    decl_quals, None);
    CPO.Declare (("asdf", 0), decl_quals, Some Smtlib.bool_sort);
    CPO.Declare (("b", 0),    decl_quals, None);
    CPO.Assign (Synth, (prefix ^ "2", 1), decl_quals, 
        PO.Bexpr (PO.Equals 
            (PO.Get (ExtSource, PO.External, "a", 0),
             PO.Get (ExtSource, PO.External, "b", 0))));
    CPO.Assign (Synth, (prefix ^ "1", 1), decl_quals,
      PO.Bexpr (PO.BinBinOp (PO.And, 
        PO.GetBoolean (ExtSource, PO.External, "asdf", 0),
        PO.GetBoolean (Synth, PO.Delay, prefix ^ "2", 1))));
    CPO.Assert (CPO.Not (CPO.Id (prefix ^ "1", 1)));
    CPO.Return CPO.True        
  ] in 
  assert_raises (Mock.StaticErrors.LoggedPathNoRandomization path_no_randomization)
    (fun () -> eval_cpo_prog cfg p8)

let test_causal_suff_1 ctxt = 
  let open Config in
  let open BT in  
  assert_raises 
    (Mock.StaticErrors.CausalSufficiencyError "^fvid1_1")
    (fun _ -> eval_cpo_prog cfg causal_suff_1) 

let test_causal_suff_2 ctxt = 
  let open Config in
  let open BT in  
  assert_raises 
    (Mock.StaticErrors.CausalSufficiencyError "^fvid2_1")
    (fun _ -> eval_cpo_prog cfg causal_suff_2)
    
let test_heirarchical ctxt = 
  let cfg = Mock.POConfig.load_annotations_json 
    "{userid : {card : \"high\"}}" in 
  let is = eval_cpo_prog cfg p10 in 
  let open BT in 
  let weights = PO.Cexpr (PO.POArray (Container, [
      PO.Cexpr (PO.POArray (Number, [
        PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 10)));
        PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 5)))]));
      PO.Cexpr (PO.POArray (Number, [
        PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (3, 10)));
        PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (2, 5)))]))])) in 
  let choices = PO.Cexpr (PO.POArray (Container, [
      PO.Cexpr (PO.POArray (Number, [
        PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (4, 1)));
        PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (3, 1)))]));
      PO.Cexpr (PO.POArray (Number, [
        PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (2, 1)));
        PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1, 1)))]))])) in 
  let consts = CPO.Sigma.empty 
    (* |> CPO.Sigma.add "weights" weights 
    |> CPO.Sigma.add "choices" choices  *)
    in 
  let should_be = [
    [(CPO.Delta.empty
      |> CPO.Delta.add "weights" weights
      |> CPO.Delta.add "choices" choices
      |> CPO.Delta.add "bar" (PO.Bexpr (PO.POBoolean true)) 
      |> CPO.Delta.add "baz" (PO.Bexpr (PO.POBoolean true))
      |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber 
          (Oratio.ReducedRatio (2, 1)))),
      Oratio.ReducedRatio (9, 100),
      CPO.Phi.empty
     ); (CPO.Delta.empty 
      |> CPO.Delta.add "weights" weights
      |> CPO.Delta.add "choices" choices
      |> CPO.Delta.add "bar" (PO.Bexpr (PO.POBoolean true)) 
      |> CPO.Delta.add "baz" (PO.Bexpr (PO.POBoolean true))
      |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber 
          (Oratio.ReducedRatio (1, 1)))),
      Oratio.ReducedRatio (3, 25),
      CPO.Phi.empty
     ); (CPO.Delta.empty 
      |> CPO.Delta.add "weights" weights
      |> CPO.Delta.add "choices" choices
      |> CPO.Delta.add "bar" (PO.Bexpr (PO.POBoolean true)) 
      |> CPO.Delta.add "baz" (PO.Bexpr (PO.POBoolean false))
      |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber 
          (Oratio.ReducedRatio (4, 1)))),
      Oratio.ReducedRatio (3, 50),
      CPO.Phi.empty
     ); (CPO.Delta.empty
      |> CPO.Delta.add "weights" weights
      |> CPO.Delta.add "choices" choices
      |> CPO.Delta.add "bar" (PO.Bexpr (PO.POBoolean true)) 
      |> CPO.Delta.add "baz" (PO.Bexpr (PO.POBoolean false))
      |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber 
          (Oratio.ReducedRatio (3, 1)))),
      Oratio.ReducedRatio (2, 25),
      CPO.Phi.empty
     ); (CPO.Delta.empty
      |> CPO.Delta.add "weights" weights
      |> CPO.Delta.add "choices" choices
      |> CPO.Delta.add "bar" (PO.Bexpr (PO.POBoolean false)) 
      |> CPO.Delta.add "baz" (PO.Bexpr (PO.POBoolean true))
      |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber 
          (Oratio.ReducedRatio (2, 1)))),
      Oratio.ReducedRatio (3, 100),
      CPO.Phi.empty
     ); (CPO.Delta.empty
      |> CPO.Delta.add "weights" weights
      |> CPO.Delta.add "choices" choices
      |> CPO.Delta.add "bar" (PO.Bexpr (PO.POBoolean false)) 
      |> CPO.Delta.add "baz" (PO.Bexpr (PO.POBoolean true))
      |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber 
          (Oratio.ReducedRatio (1, 1)))),
      Oratio.ReducedRatio (3, 50),
      CPO.Phi.empty
     ); (CPO.Delta.empty
      |> CPO.Delta.add "weights" weights
      |> CPO.Delta.add "choices" choices
      |> CPO.Delta.add "bar" (PO.Bexpr (PO.POBoolean false)) 
      |> CPO.Delta.add "baz" (PO.Bexpr (PO.POBoolean false))
      |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber 
          (Oratio.ReducedRatio (4, 1)))),
      Oratio.ReducedRatio (1, 50),
      CPO.Phi.empty
     ); (CPO.Delta.empty
      |> CPO.Delta.add "weights" weights
      |> CPO.Delta.add "choices" choices
      |> CPO.Delta.add "bar" (PO.Bexpr (PO.POBoolean false)) 
      |> CPO.Delta.add "baz" (PO.Bexpr (PO.POBoolean false))
      |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber 
          (Oratio.ReducedRatio (3, 1)))),
      Oratio.ReducedRatio (1, 25),
      CPO.Phi.empty
     ); 
    ], (consts, CPO.Phi.empty)
  ] in 
  (* print_cpo_sem is; *)
  semantics_equal is should_be

let test_ext_inference log ctxt = 
  if log then Logging.turn_on Logging.Semantics; Log.set_log_level Log.DEBUG;
  let cfg = Mock.POConfig.load_annotations_json "{extRandFn : {randomness: \"rand\", unit: \"unit\"}, 
    someid : {card : \"high\"}}" in 
  let is = eval_cpo_prog cfg p12 in 
  let rand_info = {
    PO.salt = PO.POString "abc";
    PO.unit_arg = "unit";
    PO.unit_value = PO.Id "some"
  } in 
  let should_be = [
    ([
      CPO.Delta.empty
        |> CPO.Delta.add "abc" (PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (1234, 1))))
        |> CPO.Delta.add "foo" (PO.Sexpr (PO.POString "a"))
        |> CPO.Delta.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean true))
        |> CPO.Delta.add (prefix ^ "2") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Delta.add (prefix ^ "3") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Delta.add (prefix ^ "4") (PO.Bexpr (PO.POBoolean true))
      , Oratio.neg_one, CPO.Phi.empty ;
      CPO.Delta.empty 
        |> CPO.Delta.add "abc" (PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (2345, 1))))
        |> CPO.Delta.add "foo" (PO.Sexpr (PO.POString "b"))
        |> CPO.Delta.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Delta.add (prefix ^ "2") (PO.Bexpr (PO.POBoolean true))
        |> CPO.Delta.add (prefix ^ "3") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Delta.add (prefix ^ "4") (PO.Bexpr (PO.POBoolean true))
      , Oratio.neg_one, CPO.Phi.empty ;
      CPO.Delta.empty 
        |> CPO.Delta.add "abc" (PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (3456, 1))))
        |> CPO.Delta.add "foo" (PO.Sexpr (PO.POString "c")) 
        |> CPO.Delta.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Delta.add (prefix ^ "2") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Delta.add (prefix ^ "3") (PO.Bexpr (PO.POBoolean true))
        |> CPO.Delta.add (prefix ^ "4") (PO.Bexpr (PO.POBoolean true))
      , Oratio.neg_one, CPO.Phi.empty ;
      CPO.Delta.empty 
        (* |> CPO.Delta.add "abc" (PO.Aexpr (PO.CustomNumber (
            "extRandFn", [], Some rand_info))) *)
        |> CPO.Delta.add "foo" (PO.Sexpr (PO.POString "d"))
      , Oratio.neg_one
      , CPO.Phi.empty
        |> CPO.Phi.add (PO.Bexpr (PO.Not (PO.BinNumOp (PO.AEquals, 
            PO.PONumber (Oratio.ReducedRatio (1234, 1)),
            PO.GetNumber (Source, PO.Random, "abc", 1)))))
        |> CPO.Phi.add (PO.Bexpr (PO.Not (PO.BinNumOp (PO.AEquals, 
            PO.PONumber (Oratio.ReducedRatio (2345, 1)),
            PO.GetNumber (Source, PO.Random, "abc", 1)))))
        |> CPO.Phi.add (PO.Bexpr (PO.Not (PO.BinNumOp (PO.AEquals, 
            PO.PONumber (Oratio.ReducedRatio (3456, 1)),
            PO.GetNumber (Source, PO.Random, "abc", 1)))))
        |> CPO.Phi.add (PO.Bexpr (PO.BinNumOp (PO.AEquals, 
            PO.GetNumber (SrcUnknown, PO.Delay, "abc", 1),
            PO.CustomNumber ("extRandFn", [], Some rand_info))))
        |> CPO.Phi.add (PO.Bexpr (PO.BinNumOp (PO.Lt, 
               PO.GetNumber (Source, PO.Random, "abc", 1),
               PO.PONumber (Oratio.ReducedRatio (5000, 1)))));
      CPO.Delta.empty 
        (* |> CPO.Delta.add "abc" (PO.Aexpr (PO.CustomNumber (
            "extRandFn", [], Some rand_info))) *)
        |> CPO.Delta.add "foo" (PO.Sexpr (PO.POString "e"))
      , Oratio.neg_one
      , CPO.Phi.empty
        |> CPO.Phi.add (PO.Bexpr (PO.Not (PO.BinNumOp (PO.AEquals, 
            PO.PONumber (Oratio.ReducedRatio (1234, 1)),
            PO.GetNumber (Source, PO.Random, "abc", 1)))))
        |> CPO.Phi.add (PO.Bexpr (PO.Not (PO.BinNumOp (PO.AEquals, 
            PO.PONumber (Oratio.ReducedRatio (2345, 1)),
            PO.GetNumber (Source, PO.Random, "abc", 1)))))
        |> CPO.Phi.add (PO.Bexpr (PO.Not (PO.BinNumOp (PO.AEquals, 
            PO.PONumber (Oratio.ReducedRatio (3456, 1)),
            PO.GetNumber (Source, PO.Random, "abc", 1)))))
        |> CPO.Phi.add (PO.Bexpr (PO.BinNumOp (PO.AEquals, 
            PO.GetNumber (SrcUnknown, PO.Delay, "abc", 1),
            PO.CustomNumber ("extRandFn", [], Some rand_info))))
        |> CPO.Phi.add (PO.Bexpr (PO.Not (PO.BinNumOp (PO.Lt, 
               PO.GetNumber (Source, PO.Random, "abc", 1),
               PO.PONumber (Oratio.ReducedRatio (5000, 1))))))
      ], 
    (CPO.Sigma.empty, CPO.Phi.empty));
  ] in 
  assert_equal (List.length is) 1; 
  (*Printf.printf "Number of treatments: %d\n" (List.hd is |> fst |> List.length);
  print_cpoprog (transform_program cfg p12); *)
  (* print_cpo_sem is; *)
  assert_equal (List.hd is |> fst |> List.length) 5;
  semantics_equal is should_be;
  Logging.turn_off Logging.Semantics; Log.set_log_level Log.FATAL

let test_cardinality_p13 ctxt = 
  assert_raises 
    (Mock.StaticErrors.UnitLowCardinality "banner")
    (fun () -> eval_cpo_prog cfg p13)

let test_p16b ctxt = 
  let is = eval_cpo_prog cfg p16b in 
  let should_be = [
    ([(CPO.Delta.add "free_trade_ad" (PO.Bexpr (PO.POBoolean true)) CPO.Delta.empty
       , Oratio.ReducedRatio (4, 5)
       , CPO.Phi.empty);
       (CPO.Delta.add "free_trade_ad" (PO.Bexpr (PO.POBoolean false)) CPO.Delta.empty
       , Oratio.ReducedRatio (1, 5)
       , CPO.Phi.empty)],
      (CPO.Sigma.empty
        |> CPO.Sigma.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean true))
        |> CPO.Sigma.add "country" (PO.Sexpr (PO.POString "USA")), 
       CPO.Phi.empty
        |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals, 
            PO.GetBoolean (SrcUnknown, PO.Delay, prefix ^ "2", 1), 
            PO.BinStrOp (PO.SEquals, 
              PO.GetString (Source, PO.Delay, "country", 1),
              PO.POString "Canada"))))
        |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals, 
            PO.GetBoolean (SrcUnknown, PO.Delay, prefix ^ "3", 1), 
            PO.BinStrOp (PO.SEquals, 
              PO.GetString (Source, PO.Delay, "country", 1),
              PO.POString "Mexico"))))  
        )
      );
    ([(CPO.Delta.add "free_trade_ad" (PO.Bexpr (PO.POBoolean true)) CPO.Delta.empty
       , Oratio.ReducedRatio (1, 2)
       , CPO.Phi.empty);
       (CPO.Delta.add "free_trade_ad" (PO.Bexpr (PO.POBoolean false)) CPO.Delta.empty
       , Oratio.ReducedRatio (1, 2)
       , CPO.Phi.empty)],
      (CPO.Sigma.empty
        |> CPO.Sigma.add "country" (PO.Sexpr (PO.POString "Canada"))
        |> CPO.Sigma.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Sigma.add (prefix ^ "2") (PO.Bexpr (PO.POBoolean true)), 
       CPO.Phi.empty
        |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals, 
             PO.GetBoolean (SrcUnknown, PO.Delay, prefix ^ "3", 1), 
             PO.BinStrOp (PO.SEquals, 
               PO.GetString (Source, PO.Delay, "country", 1),
               PO.POString "Mexico"))))));  
    ([(CPO.Delta.add "free_trade_ad" (PO.Bexpr (PO.POBoolean true)) CPO.Delta.empty
       , Oratio.ReducedRatio (7, 10)
       , CPO.Phi.empty);
       (CPO.Delta.add "free_trade_ad" (PO.Bexpr (PO.POBoolean false)) CPO.Delta.empty
       , Oratio.ReducedRatio (3, 10)
       , CPO.Phi.empty)],
      (CPO.Sigma.empty
        |> CPO.Sigma.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Sigma.add (prefix ^ "2") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Sigma.add (prefix ^ "3") (PO.Bexpr (PO.POBoolean true))
        |> CPO.Sigma.add "country" (PO.Sexpr (PO.POString "Mexico")), 
        CPO.Phi.empty));
  ] in 
  (*assert_equal (List.length is) 3;*)
  (* print_cpo_sem is; *)
  (* print_cpo_sem should_be; *)
  semantics_equal is should_be  

let test_guard ctxt = 
  let is = eval_cpo_prog cfg p19 in 
  let should_be = [
    [ (CPO.Delta.empty
        |> CPO.Delta.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean true))
        |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber Oratio.zero)) 
        |> CPO.Delta.add "bar" (PO.Sexpr (PO.POString "b")),
       Oratio.ReducedRatio (1, 3),
       CPO.Phi.empty);
      (CPO.Delta.empty
        |> CPO.Delta.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber Oratio.one)) 
        |> CPO.Delta.add "bar" (PO.Sexpr (PO.POString "a")),
       Oratio.ReducedRatio (1, 3),
       CPO.Phi.empty);
      (CPO.Delta.empty
        |> CPO.Delta.add (prefix ^ "1") (PO.Bexpr (PO.POBoolean false))
        |> CPO.Delta.add "foo" (PO.Aexpr (PO.PONumber (Oratio.ratio_of_int 2))) 
        |> CPO.Delta.add "bar" (PO.Sexpr (PO.POString "a")),
       Oratio.ReducedRatio (1, 3),
       CPO.Phi.empty);
       ], 
      (CPO.Sigma.empty, CPO.Phi.empty)
  ] in 
  (* print_cpo_sem is; print_cpo_sem should_be; *)
  semantics_equal is should_be

let test_trivial_failure ctxt = 
  (* This thing actually throws a different RandomVariableChoiceFailure, 
     which is why it is written in this hack way until I fix it. *)
  let failed = ref false in 
  try 
    ignore (eval_cpo_prog cfg p25)
  with _ -> failed := true;
  assert_bool 
    "Did not raise a random variable choice failure"
    !failed


let test_positivity ctxt = 
  let open Syntax in 
  assert_raises 
    ~msg:"Positivity error (zero probability for some choice)."
    (Mock.StaticErrors.PositivityError 
      ("hide_feature", Bexpr (POBoolean true)))
    (fun () -> eval_cpo_prog cfg p30)

let test_not_found ctxt = 
  let open Syntax in 
  assert_raises 
    ~msg:"Positivity error (zero probability for some choice)."
    (Mock.StaticErrors.PositivityError 
      ("in_experiment", Bexpr (POBoolean false)))
    (fun () -> eval_cpo_prog cfg p27)

let test_icse_example log ctxt =
  if log then Logging.turn_on Logging.Semantics; Log.set_log_level Log.DEBUG;
  let cfg = Mock.POConfig.load_annotations_json "{
    deviceid : {
        card : \"high\"
    },
    userid : {
        card : \"high\"
    },
    getContext : {
        dynamic : \"tv\"
    },
    country : {
      domain: \"string\"
    }
}" in 
  let is = eval_cpo_prog cfg icse_example in
  let open BT in 
  let label_dynamic_policy = "dynamic_policy" in 
  let true_expr = PO.Bexpr (PO.POBoolean true) in 
  let false_expr = PO.Bexpr (PO.POBoolean false) in 
    let label_weights = "weights" in 
  (* again, loss of info for source and mode *) 
  let get_weights = 
    PO.GetContainer (SrcUnknown, PO.Delay, label_weights, 1, Unknown) in 
  let label_choices = "choices" in 
  let get_choices = 
    PO.GetContainer (SrcUnknown, PO.Delay, label_choices, 1, Unknown) in 
  let label_max_bitrate = "max_bitrate" in 
  let max_bitrate_dynamic = PO.RandomNumber (
    PO.GetContainer (Source, PO.Delay, label_weights, 1, Number),
    PO.GetContainer (Source, PO.Delay, label_choices, 1, Number), 
    PO.Userid, PO.POString label_max_bitrate) in 
  let get_max_bitrate = 
    (* for some reason this is returning as SrcUnknown instead of Source 
       and Delay instead of Random. However, at this point in the analysis it 
       doesn't matter, so long as the expressions are in the right places. *)
    PO.GetNumber (SrcUnknown, PO.Delay, label_max_bitrate, 1) in 
  let label_context = "context" in 
  let get_context =
    PO.Get (SrcUnknown, PO.Delay, label_context, 1) in
  let get_context_fn = PO.CustomExpr ("getContext", [
      ("deviceid", PO.Get (ExtSource, PO.External, "deviceid", 0));
      ("userid", PO.Get (ExtSource, PO.External, "userid", 0))
    ], None) in 
  let label_get_bandit_weights_fn = "getBanditWeights" in 
  let get_bandit_weights = PO.CustomContainer (label_get_bandit_weights_fn, [
      (label_context, get_context)
    ], Unknown, None) in 
  let label_get_bandit_choices_fn = "getBanditChoices" in 
  let get_bandit_choices = PO.CustomContainer (label_get_bandit_choices_fn, [
      ("context", get_context)
    ], Number, None) in 
  let label_emerging_market = "emerging_market" in 
  let label_established_market = "established_market" in 
  let four_hundred_expr = 
    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (400, 1))) in 
  let seven_fifty_expr = 
    PO.Aexpr (PO.PONumber (Oratio.ReducedRatio (750, 1))) in 

  let get_fvid1 = PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid1", 1) in 
  let get_country = PO.GetString (Config.ExtSource, PO.External, "country", 0) in
  let get_fvid2 = PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid2", 1) in
  let get_fvid3 = PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid3", 1
  ) in 
  let get_fvid4 = PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid4", 1
  ) in 
  let get_emerging_market = PO.GetBoolean (Config.SrcUnknown, PO.Delay,
        label_emerging_market, 1) in 
  let get_established_market = PO.GetBoolean (Config.SrcUnknown, PO.Delay,
        label_established_market, 1) in

  let open CPO in 

  let should_be = [
    [   CPO.Delta.empty
         |> CPO.Delta.add label_dynamic_policy true_expr,
        Oratio.neg_one, 
        CPO.Phi.empty
        |> CPO.Phi.add 
        (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "choices",
         1, Po_basetypes.Unknown)),
      (Po_syntax.CustomContainer ("getBanditChoices",
         [("context",
           (Po_syntax.Get (Config.Source, Po_syntax.Delay, "context", 1)));
           ("userid",
            (Po_syntax.Get (Config.ExtSource, Po_syntax.External, "userid", 0
               )))
           ],
         Po_basetypes.Number, None))
      )))
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "choices",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.Source, Po_syntax.Delay, "choices", 1,
         Po_basetypes.Unknown))
      )))
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "weights",
         1, Po_basetypes.Unknown)),
      (Po_syntax.CustomContainer ("getBanditWeights",
         [("context",
           (Po_syntax.Get (Config.Source, Po_syntax.Delay, "context", 1)));
           ("userid",
            (Po_syntax.Get (Config.ExtSource, Po_syntax.External, "userid", 0
               )))
           ],
         Po_basetypes.Unknown, None))
      )))
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "weights",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.Source, Po_syntax.Delay, "weights", 1,
         Po_basetypes.Unknown))
      )))
      
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinNumOp (Po_syntax.AEquals,
      (Po_syntax.GetNumber (Config.SrcUnknown, Po_syntax.Delay,
         "max_bitrate", 1)),
      (Po_syntax.RandomNumber (
         (Po_syntax.GetContainer (Config.Source, Po_syntax.Delay, "weights",
            1, Po_basetypes.Number)),
         (Po_syntax.GetContainer (Config.Source, Po_syntax.Delay, "choices",
            1, Po_basetypes.Number)),
         Po_syntax.Userid, (Po_syntax.POString "max_bitrate")))
      )))
      
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinNumOp (Po_syntax.AEquals,
      (Po_syntax.GetNumber (Config.SrcUnknown, Po_syntax.Delay,
         "max_bitrate", 6)),
      (Po_syntax.GetNumber (Config.Source, Po_syntax.Random, "max_bitrate", 1
         ))
      )))
      ],
    (CPO.Sigma.empty, 
     CPO.Phi.empty 
     |> CPO.Phi.add (PO.Bexpr (PO.Equals (get_context, get_context_fn)))
     |> CPO.Phi.add 
          (PO.Bexpr (PO.BinBinOp (PO.BEquals, 
            get_fvid1,
            PO.BinStrOp (PO.SEquals, get_country, PO.POString "BR"))))
     |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals, 
          get_fvid2, 
          PO.BinStrOp (PO.SEquals,
            get_country,
            PO.POString "IN"))))
     |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          get_fvid3,
          PO.BinStrOp (PO.SEquals, get_country, PO.POString "CA"))))
     |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          get_fvid4,
          PO.BinStrOp (PO.SEquals, get_country, PO.POString "US"))))
          
     |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          get_emerging_market,
          PO.BinBinOp (PO.Or, 
            (* Propagation isn't perfect, but it doesn't affect analyses *)
            PO.GetBoolean (Config.Synth, PO.Delay, "^fvid2", 1),
            PO.GetBoolean (Config.Synth, PO.Delay, "^fvid1", 1)))))
     |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
           get_established_market,
           PO.BinBinOp (PO.Or, 
             PO.GetBoolean (Config.Synth, PO.Delay, "^fvid4", 1), 
             PO.GetBoolean (Config.Synth, PO.Delay, "^fvid3", 1))))));
    [   CPO.Delta.empty
         |> CPO.Delta.add label_dynamic_policy false_expr
         |> CPO.Delta.add label_max_bitrate four_hundred_expr,
        Oratio.neg_one,
        CPO.Phi.empty
        |> CPO.Phi.add 
      (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "choices",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "choices", 0, Po_basetypes.Unknown))
      )))
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "weights",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "weights", 0, Po_basetypes.Unknown))
      )));
      (* This phi needs choices and weights *)
      CPO.Delta.empty
      |> CPO.Delta.add label_dynamic_policy false_expr
      |> CPO.Delta.add label_max_bitrate seven_fifty_expr,
      Oratio.neg_one, 
      CPO.Phi.empty
      |> CPO.Phi.add 
      (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "choices",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "choices", 0, Po_basetypes.Unknown))
      )))
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "weights",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "weights", 0, Po_basetypes.Unknown))
      )))
    ],
    (CPO.Sigma.empty
      |> CPO.Sigma.add label_emerging_market (PO.Bexpr (PO.POBoolean true)),
     CPO.Phi.empty
      |> CPO.Phi.add (PO.Bexpr (PO.Equals (
          PO.Get (Config.SrcUnknown, PO.Delay, "context", 1),
          PO.CustomExpr ("getContext", [
            ("deviceid",
             PO.Get (Config.ExtSource, PO.External, "deviceid", 0));
            ("userid",
             PO.Get (Config.ExtSource, PO.External, "userid", 0))
           ],
         None))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
         PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid1", 1),
         PO.BinStrOp (PO.SEquals,
           PO.GetString (Config.ExtSource, PO.External, "country", 0),
           PO.POString "BR"))))
      |> Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
         PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid2", 1),
         PO.BinStrOp (PO.SEquals,
           PO.GetString (Config.ExtSource, PO.External, "country", 0),
           PO.POString "IN"))))
      |> Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
         PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid3", 1),
         PO.BinStrOp (PO.SEquals,
           PO.GetString (Config.ExtSource, PO.External, "country", 0),
           PO.POString "CA"))))
      |> Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
         PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid4", 1),
         PO.BinStrOp (PO.SEquals,
           PO.GetString (Config.ExtSource, Po_syntax.External, "country", 0),
           PO.POString "US"))))
      |> Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
         PO.GetBoolean (Config.SrcUnknown, PO.Delay, "established_market", 1),
         PO.BinBinOp (PO.Or,
           PO.GetBoolean (Config.Synth, PO.Delay, "^fvid4", 1),
           PO.GetBoolean (Config.Synth, PO.Delay, "^fvid3", 1))))));
    [   CPO.Delta.empty
           |> CPO.Delta.add label_dynamic_policy false_expr
           |> CPO.Delta.add label_max_bitrate four_hundred_expr,
          Oratio.neg_one,
          CPO.Phi.empty
          |> CPO.Phi.add 
      (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "choices",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "choices", 0, Po_basetypes.Unknown))
      )))
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "weights",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "weights", 0, Po_basetypes.Unknown))
      )));
        (* This phi needs choices and weights *)
        CPO.Delta.empty
        |> CPO.Delta.add label_dynamic_policy false_expr
        |> CPO.Delta.add label_max_bitrate seven_fifty_expr,
        Oratio.neg_one, 
        CPO.Phi.empty
        |> CPO.Phi.add 
      (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "choices",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "choices", 0, Po_basetypes.Unknown))
      )))
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "weights",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "weights", 0, Po_basetypes.Unknown))
      )))
      ],
    (CPO.Sigma.empty
      |> CPO.Sigma.add label_emerging_market false_expr
      |> CPO.Sigma.add label_established_market true_expr, 
     CPO.Phi.empty
      |> CPO.Phi.add (PO.Bexpr (PO.Equals (
          PO.Get (Config.SrcUnknown, PO.Delay, "context", 1),
          PO.CustomExpr ("getContext",
            [("deviceid",
              PO.Get (Config.ExtSource, PO.External, "deviceid", 0));
             ("userid",
              PO.Get (Config.ExtSource, PO.External, "userid", 0))
            ],
            None))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid1", 1),
          PO.BinStrOp (PO.SEquals,
            PO.GetString (Config.ExtSource, PO.External, "country", 0),
            PO.POString "BR"))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid2", 1),
          PO.BinStrOp (PO.SEquals,
            PO.GetString (Config.ExtSource, PO.External, "country", 0),
            PO.POString "IN"))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid3", 1),
          PO.BinStrOp (PO.SEquals,
            PO.GetString (Config.ExtSource, PO.External, "country", 0),
            PO.POString "CA"))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid4", 1),
          PO.BinStrOp (PO.SEquals,
            PO.GetString (Config.ExtSource, PO.External, "country", 0),
            PO.POString "US")))));
    [
            CPO.Delta.empty
            |> CPO.Delta.add label_dynamic_policy false_expr
            |> CPO.Delta.add label_max_bitrate four_hundred_expr,
           Oratio.neg_one,
           CPO.Phi.empty
           |> CPO.Phi.add 
      (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "choices",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "choices", 0, Po_basetypes.Unknown))
      )))
      |> CPO.Phi.add (Po_syntax.Bexpr
   (Po_syntax.BinCtrOp (Po_syntax.CEquals,
      (Po_syntax.GetContainer (Config.SrcUnknown, Po_syntax.Delay, "weights",
         2, Po_basetypes.Unknown)),
      (Po_syntax.GetContainer (Config.ExtSource, Po_syntax.External,
         "weights", 0, Po_basetypes.Unknown))
      )))
    ], 
    (CPO.Sigma.empty 
      |> CPO.Sigma.add label_emerging_market false_expr
      |> CPO.Sigma.add label_established_market false_expr, 
     CPO.Phi.empty 
      |> CPO.Phi.add (PO.Bexpr (PO.Equals (
          PO.Get (Config.SrcUnknown, PO.Delay, "context", 1),
          PO.CustomExpr ("getContext", [ 
            ("deviceid",
             PO.Get (Config.ExtSource, PO.External, "deviceid", 0));
            ("userid",
             PO.Get (Config.ExtSource, PO.External, "userid", 0))
           ],
         None))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid1", 1),
          PO.BinStrOp (PO.SEquals,
            PO.GetString (Config.ExtSource, PO.External, "country", 0),
            PO.POString "BR"))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid2", 1),
          PO.BinStrOp (PO.SEquals,
            PO.GetString (Config.ExtSource, PO.External, "country", 0),
            PO.POString "IN"))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid3", 1),
          PO.BinStrOp (PO.SEquals,
            PO.GetString (Config.ExtSource, PO.External, "country", 0),
            PO.POString "CA"))))
      |> CPO.Phi.add (PO.Bexpr (PO.BinBinOp (PO.BEquals,
          PO.GetBoolean (Config.SrcUnknown, PO.Delay, "^fvid4", 1),
          PO.BinStrOp (PO.SEquals,
            PO.GetString (Config.ExtSource, PO.External, "country", 0),
            PO.POString "US")))))
  ]
  in
  semantics_equal is should_be;
  Logging.turn_off Logging.Semantics; Log.set_log_level Log.FATAL

let test_too_many_treatments_1 _  =
  let prog = "choices=[0,1,2,3,4,5,6,7,8,9,10,11];
  foo = uniformChoice(choices=choices, unit=userid);" in 
  assert_raises 
    (Exceptions.ToolFailures.TooManyChoices ("foo", 12))
    (fun _ -> eval_cpo_prog cfg prog)

let test_too_many_treatments_2 _ = 
  let prog = "foo = randomInteger(min=0, max=11, unit=userid);" in 
  assert_raises 
    (Exceptions.ToolFailures.TooManyChoices ("foo", 12))
    (fun _ -> eval_cpo_prog cfg prog) 
    
let suite = 
      "suite">:::[
        "test_logging">::test_logging;
        "test_semantics_no_paths">::test_semantics_no_paths;
        "test_basic_experiment">::test_basic_experiment;
        "test_logged_path_no_randomization_1">::test_logged_path_no_randomization_1;
        "test_guard_always_false">::test_guard_always_false;
        "test_external_randomness">::test_external_randomness;
        "test_external_randomness_downstream">::test_external_randomness_downstream;
        "sanity_check_p7">::sanity_check_p7;
        "sanity_check_p8">::sanity_check_p8; 
        "test_heirarchical">::test_heirarchical; 
        "test_ext_inference">::test_ext_inference false;   
        "test_cardinality_p13">::test_cardinality_p13;
        "test_p16b">::test_p16b;
        "test_guard">::test_guard;
        "test_trivial_failure">::test_trivial_failure;
        "test_positivity">::test_positivity;
        "test_not_found">::test_not_found;
        "test_icse_example">::test_icse_example false;
        "test_too_many_treatments_1">::test_too_many_treatments_1;
        "test_too_many_treatments_2">::test_too_many_treatments_2;
        "test_reset_exp">::test_reset_exp;
        "test_causal_suff_1">::test_causal_suff_1; 
        "test_causal_suff_2">::test_causal_suff_2
      ] 

let run_stuff () = 
    (* Not sure why the mock targets one isn't working. *)
    Mock.register_printers ();
    Printexc.register_printer (function 
      | Mock.StaticErrors.RandomVariableChoiceFailure (salt, num_choices) ->
        Some (Printf.sprintf 
         "Random variable having salt \"%s\" has %d choices." 
         salt num_choices)
      | Mock.StaticErrors.LoggedPathNoRandomization pi ->
        Some (Printf.sprintf ("%s\n\n" ^^
          "%s\n")
          (Mock.POCorepo.Format.string_of_path pi)
          (Mock.POCorepo.Format.ast_string_of_path pi)
          )
      | Mock.Parse.Malformed_unit s -> 
        Some (Po_format.string_of_expr s)
      | _ -> None);
    (* Log.set_log_level Log.DEBUG; *)
    run_test_tt_main suite

let () = 
  Printf.printf "Running %s" __FILE__;
  Mock.Transform.Corepo.toggle_mock ();
  (* run_test_tt_main suite *)
  run_stuff ()