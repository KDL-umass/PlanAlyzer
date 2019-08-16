open Core

(** Environment variable holding the global configuration file. *)
let _PLANALYZER_CONFIG = "PLANALYZER_CONFIG"
let output_dir = ref "OUTPUT"

let print_output_file filename content = 
  Utils.mkdir !output_dir;
  let filename = !output_dir ^ "/" ^ filename in 
  Utils.string_to_file filename content 

module Logger = Logging.Make(struct 
    let file = __FILE__
    let phase = Logging.All
  end)

let t_parsim =
  Command.Spec.Arg_type.create
    (fun pname ->
      Sexp.of_string pname |> Inputs.parsimony_types_of_sexp)

let t_lang = 
  Command.Spec.Arg_type.create
    (fun lname ->
      Sexp.of_string lname |> Inputs.language_of_sexp) 
  
let t_phase =
  Command.Spec.Arg_type.create
   (fun pname -> 
    Sexp.of_string pname |> Logging.phase_of_sexp)

let t_config = 
  Command.Spec.Arg_type.create
   (fun cname ->
    Sexp.of_string cname |> Inputs.config_input_of_sexp)

let spec =
  let open Command.Spec in
  empty
  +> anon ("filename" %: file)
  +> flag "-expid"        (optional int)      ~doc:"int Numeric identifier for the experiment (for database storage)"
  +> flag "-config"       (optional file)     ~doc:"file Overwrite any global configs with the contents of the local config file"
  +> flag "-config-type"  (optional t_config) ~doc:"string The file format of the configuration files {ConfigJson|ConfigYAML}"
  (* Using optional bool instead of no_arg for flags, since we are setting them globally -- need an option type. See inputs.ml 
     TODO: make this fully functional, with no global refs?
   *)
  +> flag "-html"         no_arg              ~doc:" Output as an html page"
  +> flag "-report"       no_arg              ~doc:" Print static analysis data for the experiment designer"
  +> flag "-analysis"     no_arg              ~doc:" Print data frames for analysis"
  +> flag "-assertions"   no_arg              ~doc:" Print assertions to be used by the runtime system"
  +> flag "-parsimony"    (optional t_parsim) ~doc:" whether to minimize the output for estimators {roots, leaves}."
  +> flag "-nowarn"       no_arg              ~doc:" Whether to print warnings"
  +> flag "-debug"        (optional t_phase)  ~doc:" Print debugging statements"
  +> flag "-time"         no_arg              ~doc:" Collect timing information"
  +> flag "-lang"         (optional t_lang)   ~doc:"string The input language to analyze {PlanOutJson|PlanOutRaw}" 
  +> flag "-pretty"       no_arg              ~doc:" Whether to pretty print errors"
  +> flag "-maxchoices"   (optional int)      ~doc:" The maximum number of finite choices for pairwise comparison. Default is 20."
  +> flag "-humanoutput"  no_arg              ~doc:" Print human-readable output (in addition to tables)."


(** Loads the json blob in from a file. *)
let load_json filename = 
  let open Yojson in 
  try 
    Safe.from_file filename |> Safe.to_basic 
  with Sys_error e -> printf "%s\n" e; Yojson.Basic.from_string "{}"

let get_global_config_file_contents () =
  let open Core.In_channel in 
  match Sys.getenv _PLANALYZER_CONFIG with 
  | Some fname -> read_all fname
  | None -> Printf.printf "WARNING: $%s not set.\n" _PLANALYZER_CONFIG; ""

let get_local_config_file_contents filename =
  Core.In_channel.read_all filename

(** First loads in the global configuration file, then the local. 
    If either doesn't exist, it loads an empty config object. *)
let load_config filename = 
  match !Inputs.lang with 
  | Inputs.PlanOutRaw
  | Inputs.PlanOutJson -> 
    let open Targets.PlanOut in 
    let global_config = get_global_config_file_contents () in 
    let local_config = (match filename with 
        | "" -> ""
        | _ ->
          Logger.print_debug __LINE__ "%s" filename;
          get_local_config_file_contents filename) in 
    let load_fn = (match !Inputs.cfg with 
                   | Inputs.ConfigJson -> POConfig.load_annotations_json
                   | Inputs.ConfigYAML -> POConfig.load_annotations_yaml) in 
    load_fn global_config
    |> (fun init -> load_fn ~init:init local_config) 
  | _ -> raise (Exceptions.ToolFailures.NYI 
    "planalyzer currently only supports PlanOut json or raw (-lang {PlanOutJson|PlanOutRaw}) input") 

let planout_normalize_program config prog = 
  let open Targets.PlanOut in 
  let timefn fn = 
    if !Inputs.time 
    then Performance.time Logging.Normalize fn 
    else fn ()
    in 
  let (_, normed_prog) as retval = 
    (fun _ -> Normalize.normalize config prog)
    |> timefn in 
  print_output_file "normed_program" 
    (Ast.Format.string_of_program normed_prog);
  retval 

let planout_build_ddg prog = 
  let open Targets.PlanOut in 
  let timefn fn = 
    if !Inputs.time 
    then Performance.time Logging.Ddg fn 
    else fn ()
    in
  let ddg = (fun _ -> DDG.build_dependence_graph prog)
    |> timefn in 
  print_output_file "ddg" 
    (DDG.string_of_graph ~max_len:1000 ddg);
  ddg

let planout_make_corepo ddg config prog = 
  let open Targets.PlanOut in 
  let timefn fn = 
    if !Inputs.time 
    then Performance.time Logging.Corepo fn 
    else fn ()
    in
  let corepo = (fun _ -> Tform.transform ddg config prog)
    |> timefn in
  print_output_file "corepo" 
    (POCorepo.Format.string_of_program corepo);
  corepo


let planout_make_semantics ddg config prog = 
  let open Targets.PlanOut in 
  let timefn fn = 
    if !Inputs.time 
    then Performance.time Logging.Semantics fn 
    else fn ()
    in
  let semantics = timefn (fun _ -> POCorepo.eval config ddg prog) in 
  let str = POCorepo.Format.string_of_semantics_tuples semantics in 
  print_output_file "semantics" str;
  semantics

let planout_make_ate_human ddg prog semantics = 
  let open Targets.PlanOut in 
  let timefn fn = 
    if !Inputs.time 
    then Performance.time Logging.Estimators fn 
    else fn () in 
  timefn (fun _ -> 
    print_output_file "ate"
      (ATE.string_of_pairwise_contrasts ddg prog semantics))

let planout_make_ate_tables ddg prog semantics = 
  let open Targets.PlanOut in 
  let timefn fn = 
    if !Inputs.time 
    then Performance.time Logging.Estimators fn 
    else fn () in 
  timefn (fun _ -> 
    (* let conds, treatments = *)
    ATE.QueryableTables.ate_to_csv_data 
      !output_dir !Inputs.exp_id semantics 
      (* in
    print_output_file "conds.csv" conds;
    print_output_file "treatments.csv" treatments *)
  )
  
let report config prog : unit = 
  let open Targets.PlanOut in 
  let (config, normed_prog) = planout_normalize_program config prog in 
  let ddg = planout_build_ddg normed_prog in 
  let corepo_prog = planout_make_corepo ddg config normed_prog in 
  let semantics = planout_make_semantics ddg config corepo_prog in 
  planout_make_ate_tables ddg prog semantics;
  if !Inputs.human_output
  then planout_make_ate_human ddg corepo_prog semantics

let convert_and_run_planout filename : unit = 
  let to_json_string = 
    Core.In_channel.read_all filename
    |> Targets.PlanOut.Parse.exec_po_compiler in 
  let open Yojson in 
  let config = load_config !Inputs.local_config in 
  let prog = Basic.from_string to_json_string 
            |> Targets.PlanOut.Parse.make_program config in 
  report config prog 

let run_planout filename : unit = 
  let open Targets.PlanOut in 
  let json = load_json filename in 
  let config = load_config !Inputs.local_config in
  let prog = Parse.make_program config json in  
  if !Inputs.report
  then report config prog
  else Printf.printf "# Experiment %s\n%s" filename 
    (Ast.Format.string_of_program ~show_index:(!Inputs.debug <> None) prog);
  if !Inputs.time
  then print_string (Performance.report ())

let flag_dispatch _ : unit = 
  begin match !Inputs.lang with 
  | Inputs.PlanOutJson 
  | Inputs.PlanOutRaw -> 
    if !Inputs.pretty 
    then Targets.PlanOut.register_printers ()
  | _ -> () 
  end;
  (* Log.set_log_level Log.DEBUG; *)
  begin match !Inputs.debug with
  | None -> 
    let open Logging in 
    List.iter Logging.all_phases Logging.turn_off 
  | Some Logging.All -> 
    List.iter Logging.all_phases Logging.turn_on;
    Log.set_log_level Log.DEBUG
  | Some phase -> 
    Logging.turn_on phase ; Log.set_log_level Log.DEBUG 
  end
  

let make_output_dir filename = 
  let dir = Filename.basename filename in 
  Utils.mkdir dir;
  output_dir := dir

let do_analysis filename exp_id config config_type html report analysis 
  assertions parismony nowarn debug time lang pretty max_choices 
  human_output
  () = 
      ignore (Inputs.set_if_input exp_id Inputs.exp_id);
      ignore (Inputs.set_if_input config Inputs.local_config);
      ignore (Inputs.set_if_input config_type Inputs.cfg);
      (*ignore (Inputs.set_if_input html Inputs.html); *)
      ignore (Inputs.set_if_input (Some report) Inputs.report);
      (* ignore (Inputs.set_if_input analysis Inputs.analysis); *)
      (* ignore (Inputs.set_if_input assertions Inputs.assertions);
      ignore (Inputs.set_if_input parismony Inputs.parsimony 
        ~convert_cmd:Config_types.parsimony_type_of_sexp);*)
      ignore (Inputs.set_if_input (Some nowarn) Inputs.nowarn);
      ignore (Inputs.set_if_input (Some debug)  Inputs.debug);
      ignore (Inputs.set_if_input (Some time)   Inputs.time);
      ignore (Inputs.set_if_input lang          Inputs.lang);
      ignore (Inputs.set_if_input (Some pretty) Inputs.pretty); 
      ignore (Inputs.set_if_input max_choices   Inputs.max_choices);
      ignore (Inputs.set_if_input (Some human_output)  Inputs.human_output);
      flag_dispatch ();
      make_output_dir filename;
      match !Inputs.lang with 
      | Inputs.PlanOutJson -> run_planout filename
      | Inputs.PlanOutRaw -> convert_and_run_planout filename 
      | _ -> assert false

let command =
  Command.basic_spec
    ~summary:"planalyzer is a command-line tool that statically checks input planout programs for correctness, generating estimators when possible"
    ~readme:(fun () -> "Read in a file here.")
    spec
    do_analysis
      

(** This is the main entry point. It reads in argments, sets the global
    input parameters, and dispatches on the estimator policy. *)
let () =
  let handler_fn i = 
    Core.Printexc.print_backtrace Out_channel.stderr;
    raise (Exceptions.ClassificationFailures.Interrupt i) in 
  Core.Signal.Expert.handle Core.Signal.int handler_fn;
  Core.Signal.Expert.handle Core.Signal.abrt handler_fn;
  Command.run ~version:"0.2" 
              ~build_info:"Cleaner, more performant version" 
              command; 