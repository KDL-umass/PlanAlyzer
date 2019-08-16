open Sexplib.Std

type language = PlanOutRaw | PlanOutYAML | PlanOutJson [@@deriving sexp] 
type config_input = ConfigJson | ConfigYAML [@@deriving sexp]
type parsimony_types = 
  | Roots 
  | Leaves 
  | Names of string list
 [@@deriving sexp]

let pretty = ref false

let analysis = ref false
let report = ref false
let assertions = ref false 

let sql = ref true
let experiment_name = ref ""
let exposure_table = ref ""

let human_output = ref false 
                     
let max_vars = ref (-1)
let max_paths = ref (-1)
let max_choices = ref 20

let parsimony = (ref None : parsimony_types option ref)

let nowarn = ref false
let debug = (ref None : Logging.phase option ref)

let html = ref false

let local_config = ref ""
let lang = ref PlanOutJson
let cfg = ref ConfigJson
let time = ref false

let exp_id = ref 0

let set_if_input ?(convert_cmd=(fun (x : 'a) -> (x : 'b)))
                 (cmd_arg : 'a option) 
                 (cmd_arg_ref : 'b ref)
                 : bool =
    match cmd_arg with 
    | Some thing -> cmd_arg_ref := convert_cmd thing; true
    | None -> false