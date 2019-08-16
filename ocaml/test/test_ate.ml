open OUnit2
open Programs_aux
open Config 

open Mock_targets.PlanOut

let make_program = make_program2 Parse.exec_po_compiler Parse.make_program 
let cfg = POConfig.load_annotations_json default_annot 

let transform p = 
  let (cfg, prog) = make_program cfg p
                    |> Normalize.normalize cfg in 
  Transform.transform   
    (Ast.PODdg.build_dependence_graph prog) cfg prog

let make_contrasts cfg p = 
  let (cfg, prog) = make_program cfg p
                    |> Normalize.normalize cfg in 
  let ddg = Ast.PODdg.build_dependence_graph prog in
  let cpo_prog = Transform.transform ddg cfg prog in
  cpo_prog
  |> Transform.Corepo.eval cfg ddg
  |> ATE.string_of_pairwise_contrasts ddg cpo_prog

let test_ate_p16 ctxt = 
  ignore (make_contrasts cfg p16)

let test_ate_p16b ctxt = 
  ignore (make_contrasts cfg p16b)

let test_ate_p10 ctxt = 
  ignore (make_contrasts cfg p10)

let test_ate_p18 ctxt = 
  let cfg = POConfig.load_annotations_json "{getRandomSegment : {randomness : \"rand\", unit : \"userid\", card : \"high\"}, \"userid\" : {card : \"high\"}}" in
  ignore (make_contrasts cfg p18)

let test_ate_dynamic_basic ctxt = 
  let cfg = POConfig.load_annotations_json "{someTimeVaryingRandomAction: {
    randomness : \"rand\",
    dynamism : \"tv\",
    unit : \"context\"},
  userid : {card : \"high\"},
  context : { card : \"high\"}}" in 
  ignore (make_contrasts cfg p28)

let test_ate_icse_paper ctxt = 
  let cfg = POConfig.load_annotations_json "{
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
  Printf.printf "%s\n" (make_contrasts cfg icse_example) 

let test_expecting_assumption_error cfg p = 
  let failed = ref false in 
  try 
    ignore (make_contrasts cfg p)
  with _ -> failed := true;
  assert_bool "make_contrasts should fail." !failed

let test_within_subjects_1 _ = 
  test_expecting_assumption_error cfg within_subjects_1
  
let test_within_subjects_2 _ = 
  test_expecting_assumption_error cfg within_subjects_2

let test_within_subjects_3 _ = 
  let cfg = POConfig.load_annotations_json "{
    userid : { card : \"high\"},
    deviceid : {card : \"high\"}
  }" in 
  test_expecting_assumption_error cfg within_subjects_3

let test_unit ctxt = 
  assert_raises 
    ~msg:"Data flow causes the unit to be low cardinality"
    (Mock_targets.PlanOut.StaticErrors.UnitLowCardinality "unit")
    (fun _ -> make_contrasts cfg test_data_flow)

let suite = 
  "suite">:::[
    "test_ate_p16">::test_ate_p16;
    "test_ate_p16b">::test_ate_p16b;
    "test_ate_p10">::test_ate_p10;
    "test_ate_p18">::test_ate_p18;
    "test_ate_dynamic_basic">::test_ate_dynamic_basic;
    "test_within_subjects_1">::test_within_subjects_1;    
    "test_within_subjects_2">::test_within_subjects_2;
    "test_within_subjects_3">::test_within_subjects_3;
    "test_ate_icse_paper">::test_ate_icse_paper;
    "test_unit">::test_unit
  ]

let () =
  register_printers ();
  Printexc.register_printer (function 
    | POCorepo.Static_errors.UnloggedPathRandomization path -> 
      Some (Printf.sprintf "Unlogged path contains randomized treatment: %s\n"
        (POCorepo.Format.string_of_path path))
    | _ -> None);
  (* Log.set_log_level Log.DEBUG; *)
  ignore (Transform.Corepo.toggle_mock ());
  Printf.printf "Running %s" __FILE__;
  run_test_tt_main suite
