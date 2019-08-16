open Sexplib.Std

type cardinality = High | Low [@@deriving sexp]
type dynamism = Const | Tv [@@deriving sexp]
type randomness = 
    | Det 
    | Rand of string list 
    | CS of {dets : int list; rands: (int * string list) list}
  [@@deriving sexp] 

type corr_t = 
  | End 
  | Exo 
[@@deriving sexp]

type origin = 
  | Source 
  | ExtSource 
  | Synth 
  | SrcUnknown
[@@deriving show]

type ssa_id = string * int [@@deriving sexp] 
let string_of_ssa_id (s, i) = Printf.sprintf "%s_%d" s i 
let ssa_id_of_string s = 
  match Str.split (Str.regexp "_") s |> List.rev with 
  | n::tl -> (Utils.join "_" Utils.identity (List.rev tl), 
    int_of_string n)
  | _ -> assert false 
let ssa_id_compare (s1, i) (s2, j) = 
  if s1 = s2 
  then compare i j 
  else compare s1 s2

exception ConfigFormatErr of string * string 
exception UnsupportedDomain
exception UnitError of string 

let make_config_format_err ~field ~msg = ConfigFormatErr (field, msg)  
module Params = Set.Make(struct
    type t = ssa_id 
    let compare = ssa_id_compare 
  end)   

module type Config_lang = sig 
    type basetype [@@deriving sexp]
    val t_default : basetype
    val basetype_of_sexp : Sexplib.Sexp.t -> basetype
    val sexp_of_basetype : basetype -> Sexplib.Sexp.t
end  

module type Config = sig
    include Config_lang
    type typequals 

    type domain = 
      | Var of basetype 
      | FnArg of (string * basetype) list 
      [@@deriving sexp] 

      type config = 
        {
            card       : cardinality   [@default Low];
            dynamism   : dynamism      [@default Const];
            randomness : randomness    [@default Det];
            domain     : domain        [@default (FnArg [])];
            codomain   : basetype      [@default t_default];
            corr_t     : corr_t option [@default None];
            unit       : string        [@default ""]
        } [@@deriving fields, sexp, make] 
        
    exception MalformedAnnotationExpression of 
      string * string * Sexplib.Sexp.t [@@deriving sexp]
    exception UnsupportedDomain

    val bindings : typequals -> (string * config) list

    val load_annotations_json : ?init:typequals -> string -> typequals
    val load_annotations_yaml : ?init:typequals -> string -> typequals

    val update_cardinality : cardinality -> config -> config
    val update_codomain : basetype -> config -> config 
    val update_domain : domain -> config -> config 
    val update_dynamism : dynamism -> config -> config 
    val update_randomness : randomness -> config -> config 
    val update_correlation: corr_t -> config -> config 

    val add_default : string -> typequals -> typequals
    val get_config : string -> typequals -> config
    val update_config : string -> config -> typequals -> typequals

    val empty : typequals
    val is_random : string -> typequals -> bool
    val get_codomain : string -> typequals -> basetype option
    val get_cardinality : string -> typequals -> cardinality option 
    val get_unit : string -> typequals -> string option

    val string_of_typequals : typequals -> string
    val string_of_config : config -> string 
end

module Make(Cfg : Config_lang) = struct 
    include Cfg

    (* open Sexplib.Conv  to get bool_of_sexp for the default syntax  *)
    type domain = 
      | Var of basetype 
      | FnArg of (string * basetype) list 
      [@@deriving sexp] 

    type config = 
      {
          card       : cardinality   [@default Low];
          dynamism   : dynamism      [@default Const];
          randomness : randomness    [@default Det];
          domain     : domain        [@default (FnArg [])];
          codomain   : basetype      [@default t_default];
          corr_t     : corr_t option [@default None];
          unit       : string        [@default ""]
      } [@@deriving fields, sexp, make] 
    
    
    (******************** TQ Env Implementation ********************)
    module TypeQuals = Map.Make(String) (* string -> config *) 
    type typequals = config TypeQuals.t 

    let bindings = TypeQuals.bindings

    let empty = TypeQuals.empty 

    let is_random (varname : string) (tq : typequals) = 
      if TypeQuals.mem varname tq
      then match (TypeQuals.find varname tq).randomness with
        | Rand _ -> true 
        | _ -> false 
      else false

    let get_codomain (varname : string) (tq : typequals) = 
      if TypeQuals.mem varname tq
      then Some (TypeQuals.find varname tq).codomain
      else None

    let get_cardinality (varname : string) (tq : typequals) = 
      if TypeQuals.mem varname tq 
      then Some (TypeQuals.find varname tq).card
      else None 

    let get_unit (varname : string) (tq : typequals) = 
      if TypeQuals.mem varname tq
      then Some (TypeQuals.find varname tq).unit 
      else None

    (******************** Module Implementation ********************)

    exception MalformedConfigFile of string
    exception UnsupportedDomain
    exception MalformedAnnotationExpression of 
      string * string * Sexplib.Sexp.t [@@deriving sexp]
  
    module YB = Yojson.Basic
    module YBU = Yojson.Basic.Util
    module Sexp = Sexplib.Sexp
  
    let find_and_default key js (def : 'a) (convert : YB.json -> 'a) =
      try 
        match YBU.member key js with
        | `Null -> def
        | v -> convert v
      with 
      | YBU.Type_error (msg, json) ->
        raise (YBU.Type_error (msg, `Assoc [(key, json)]))
  
    let type_of_json_string (convert: Sexp.t -> 't) (v : YB.json) : 't = 
      YBU.to_string v 
      |> Sexp.of_string
      |> Sexp.t_of_sexp
      |> convert
    
    let get_domain (convert : Sexp.t -> basetype) param_obj : domain =
      match YBU.member "domain" param_obj with
      | `Null -> FnArg []
      | `List tuples ->
        FnArg (List.map (function 
                  | `List [k;v] -> (
                    YBU.to_string k, type_of_json_string convert v) 
                  | _ -> assert false)
               tuples)
      | `String _ as s -> begin
        try
          Var (type_of_json_string convert s)
        with (Sexplib.Conv.Of_sexp_error _) -> raise UnsupportedDomain
      end 
      | _ -> assert false
      
    let make_config_from_json key (param_obj : YB.json) : config =
      let tmp_rand eunit sexp = match sexp with 
        | Sexp.Atom "rand" -> 
          if eunit = ""
          then raise (UnitError key)
          else Rand []
        | Sexp.Atom "det" -> Det
        | _ -> 
          raise (MalformedAnnotationExpression (key, "randomness", sexp)) in 
      try
        let fnd_def k def fn = find_and_default k param_obj def fn in 
        let card = fnd_def "card" Low 
                    (type_of_json_string cardinality_of_sexp) in
        let dyn = fnd_def "dynamism" Const 
                    (type_of_json_string dynamism_of_sexp) in
        let eunit = fnd_def "unit" "" YBU.to_string in
        let rand = fnd_def "randomness" Det 
                    (type_of_json_string (tmp_rand eunit)) in
        let corry = fnd_def "corr_t" None
                    (type_of_json_string (option_of_sexp corr_t_of_sexp)) in
        let codom = fnd_def "codomain" t_default 
                    (type_of_json_string basetype_of_sexp) in
        let dom = get_domain basetype_of_sexp param_obj in
        { card = card;
          dynamism = dyn;
          randomness = rand;
          domain = dom; 
          codomain = codom;
          corr_t = corry;
          unit = eunit
        }
      with 
      | Sexplib.Conv.Of_sexp_error (Failure msg, tag) as err -> begin
          let cos = __FILE__ ^ ".cardinality_of_sexp" in 
          let dos = __FILE__ ^ ".dynamism_of_sexp" in 
          let ros = __FILE__ ^ ".randomness_of_sexp" in 
          let bos = "planalyzer/planout/basetypes.ml.base_type_of_sexp" in
          let unexpected_sum_tag = ": unexpected sum tag" in 
          let cmsg = cos ^ unexpected_sum_tag in 
          let dmsg = dos ^ unexpected_sum_tag in 
          let bmsg = bos ^ unexpected_sum_tag in 
          let rmsg = ros ^ unexpected_sum_tag in 
          if msg = cmsg 
          then raise (MalformedAnnotationExpression (key, "cardinality", tag))
          else if msg = dmsg 
          then raise (MalformedAnnotationExpression (key, "dynamism", tag))
          else if msg = bmsg
          then raise 
            (MalformedAnnotationExpression (key, "domain/codomain", tag))
          else if msg = rmsg
          then raise 
            (MalformedAnnotationExpression (key, "randomness", tag))
          else raise err
        end
      | YBU.Type_error(msg, json) as err -> begin
          let open Yojson.Basic in 
          match json with 
          | `Assoc [(annot, `String s)] ->
            raise (MalformedAnnotationExpression 
              (key, annot, Sexplib.Sexp.of_string s))
          | `Assoc [(annot, `Int i)] ->
            raise (MalformedAnnotationExpression
              (key, annot, Sexplib.Sexp.of_string (string_of_int i)))
          | `Assoc [(annot, `Float f)] ->
            raise (MalformedAnnotationExpression
              (key, annot, Sexplib.Sexp.of_string (string_of_float f)))
          | _ -> raise err
        end

    let rec make_configs : YB.json -> (string * config) list = function
      | `Assoc [] -> []
      | `Assoc ((key, features)::t) ->
        (key, make_config_from_json key features)::(make_configs (`Assoc t))
      | `String "" -> []
      | js -> raise (MalformedConfigFile (YB.to_string js))
      
    
    let load_annotations_json ?(init=TypeQuals.empty) str =
      begin 
        try
          let json = Yojson.Safe.from_string str |> Yojson.Safe.to_basic in
          make_configs json
          |> List.fold_left (fun quals (n, c) -> TypeQuals.add n c quals) init
        with
        | Yojson.Json_error "Blank input data" -> init
        | Yojson.Json_error msg ->
          (Printf.printf "Config file is malformed: %s\n" msg;
          raise (MalformedConfigFile msg))
      end 

    let load_annotations_yaml ?(init=TypeQuals.empty) str = 
      let rec yaml_to_json (yaml: Yaml.value) : Yojson.json = match yaml with 
        | `O svlist -> `Assoc (List.map 
                                (fun (k, v) -> (k, yaml_to_json v)) 
                                svlist)
        | `A lst -> `List (List.map yaml_to_json lst)
        | `Null -> `Null
        | `Bool b -> `Bool b
        | `Float f -> `Float f
        | `String "true"  -> `Bool true
        | `String "false" -> `Bool false 
        | `String s -> `String s 
        in 
      begin 
          let parsed = Yaml.of_string str |> Rresult.R.get_ok in 
          let json_str = yaml_to_json parsed |> Yojson.to_string in 
          (* print_string json_str; *)
          load_annotations_json ~init json_str 
      end 

    let empty_config = config_of_sexp (Sexp.of_string "()")

    let update_cardinality v cf = 
      let open Cfg in 
      let {    
        dynamism   ;
        randomness ;
        domain     ;
        codomain   ;
        corr_t     ;
        unit=unitv
        } = cf in 
        {
            card       = v;
            dynamism   = dynamism;
            randomness = randomness;
            domain     = domain;
            codomain   = codomain;
            corr_t     = corr_t;
            unit       = unitv
        }
  
    let update_randomness v cf = 
      let open Cfg in 
      let {    
        card       ;
        dynamism   ;
        domain     ;
        codomain   ;
        corr_t   ;
        unit=unitv
        } = cf in 
        {
            card       = card;
            dynamism   = dynamism;
            randomness = v;
            domain     = domain;
            codomain   = codomain;
            corr_t     = corr_t;
            unit       = unitv
        }

    let update_correlation v cf = 
      let open Cfg in 
      let {    
          card       ;
          dynamism   ;
          domain     ;
          codomain   ;
          randomness ;
          unit=unitv
        } = cf in 
        {
            card       = card;
            dynamism   = dynamism;
            randomness = randomness;
            domain     = domain;
            codomain   = codomain;
            corr_t     = Some v;
            unit       = unitv
        }
      
    let update_dynamism v cf = 
      let open Cfg in 
        let {    
        card       ;
        randomness ;
        domain     ;
        codomain   ;
        corr_t     ;
        unit       ;
        } = cf in 
        {
            card       = card;
            dynamism   = v;
            randomness = randomness;
            domain     = domain;
            codomain   = codomain;
            corr_t     = corr_t;
            unit       = unit
        }

    let update_codomain (v : basetype) cf = 
      let open Cfg in 
        let {    
        card       ;
        randomness ;
        domain     ;
        dynamism   ;
        corr_t     ;
        unit       ;
        } = cf in 
        {
            card       = card;
            dynamism   = dynamism;
            randomness = randomness;
            domain     = domain;
            codomain   = v;
            corr_t     = corr_t;
            unit       = unit
        }

    let update_domain (v : domain) cf = 
      let open Cfg in 
        let {    
        card       ;
        randomness ;
        codomain     ;
        dynamism   ;
        corr_t     ;
        unit       ;
        } = cf in 
        {
            card       = card;
            dynamism   = dynamism;
            randomness = randomness;
            domain     = v;
            codomain   = codomain;
            corr_t     = corr_t;
            unit       = unit
        }
    

    let add_default name tq = TypeQuals.add name empty_config tq

    let get_config name tq = 
      if TypeQuals.mem name tq 
      then TypeQuals.find name tq
      else config_of_sexp (Sexplib.Sexp.List [])

    let update_config name cfg tq = 
      TypeQuals.add name cfg tq 
  
    let string_of_config (cf : config) : string =
      sexp_of_config cf |> Sexp.to_string
  
    let string_of_typequals (tq : typequals) : string = 
      let open Core.String in 
      TypeQuals.bindings tq
      |> List.map (fun (k, v) -> Printf.sprintf "%s: %s" k (string_of_config v))
      |> concat ~sep:"\n" 

end
  
