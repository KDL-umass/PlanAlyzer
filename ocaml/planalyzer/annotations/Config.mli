(********************************************************************************
    Specification for input config files. The current implementation only 
    handles JSON input files, but a future version should read YAML files under 
    an analogous specification as well. 

    Input spec:
    - top-level keys are all variable names
    - top-level values are dictionaries
    Each of these dictionaries may have keys that correspond to the keys in the 
    config type below.     
*******************************************************************************)

(** The cardinality of an external variable or function call. *)
type cardinality = High | Low [@@deriving sexp]
(** The dynamism of an external variable or function call. *)
type dynamism = Const | Tv [@@deriving sexp]
(** Whether a variable is randomly assigned, deterministically assigned, or a 
    a mix, depending on path (for phi nodes). *)
type randomness = 
    | Det 
    | Rand of string list 
    | CS of {dets : int list; rands : (int * string list) list}
[@@deriving sexp] 
(** Whether a variable is endogenous (End, correlated with the assignment of 
  outcome treatment), or exogenous (Exo, uncorrelated with the assignment of 
  treatment. *)
type corr_t = End | Exo [@@deriving sexp]

type origin = Source | ExtSource | Synth | SrcUnknown [@@deriving show]

type ssa_id = string * int [@@deriving sexp]
val string_of_ssa_id : ssa_id -> string 
val ssa_id_of_string : string -> ssa_id 
val ssa_id_compare : ssa_id -> ssa_id -> int 

(** The module used to hold set information about program variables, using 
    the SSA'ed ids. *)
module Params : Set.S with type elt = ssa_id
    
exception ConfigFormatErr of string * string 
exception UnsupportedDomain
exception UnitError of string 

(** Function for generating ConfigFormatErr . *)
val make_config_format_err : field:string -> msg:string -> exn

(** This module gives the base types for the input language. For an 
implementation, see targets.ml *)
module type Config_lang = sig
    (** The base types that final values in the input language evaluated down 
    to. 
    *)
    type basetype [@@deriving sexp]  

    (** The defalult base type (e.g., Top, Any, or Unknown). *) 
    val t_default : basetype  
 
    (** Conversion function from basetype to sexp. This should be automatically 
    generated from Jane Street's Sexplib and needs to be exported. 
    *)
    val basetype_of_sexp : Sexplib.Sexp.t -> basetype

    (** Conversion function from sexp to basetype. This should be automatically 
    generated from Jane Street's Sexplib and needs to be exported. 
    *)
    val sexp_of_basetype : basetype -> Sexplib.Sexp.t
end  

(** This module provides the public specification for reading in configuration 
    files, which contain type annotations and type qualifier annotations for 
    external calls or references. 
*)
module type Config = sig
    include Config_lang

    (** The type of the type qualifier environment. *)
    type typequals 

    type domain = 
        | Var of basetype 
        | FnArg of (string * basetype) list 
      [@@deriving sexp] 
 
    (** The type and type qualifier environment. Note that, unlike standard 
    types, the qualifiers do not require preservation. However, because 
    PlanAlyzer performs SSA over the input script, it can store a unique 
    snapshot of each variable, in the event that its qualifier changes. 

    Type Qualifiers:
    - card       : The cardinality of a variable 
    - dynamism   : The dynamism of a variable 
    - randomness : Whether a variable has been randomly assigned

    Types:
    - domain     : The type of the domain of a variable or a function. If the 
                   variable is a function, then the domain is a list of named 
                   parameters mapped to the domain type. If the variable is not 
                   a function, then it has a single entry pairing an empty 
                   string with the basetype.
    - codomain   : The type of a function's codomain
    
    Additional Data:
    - corr_t     : Flag from {Exo, End} indicating that the variable is expected 
                   to be correlated with treatment assignment and thus a 
                   potential confounder. These are mostly inferred. 
    - unit       : The named input parameter corresponding to the unit of 
                   randomization; only used when we have calls to external 
                   random functions
    *)
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

    (** Raised when the annotation is not of a recognized type. Arguments are 
    the key, type or type qualifier, and the  matching value *)
    exception MalformedAnnotationExpression of 
     string * string * Sexplib.Sexp.t [@@deriving sexp]
    exception UnsupportedDomain

    val bindings : typequals -> (string * config) list 

    (** Function to load annotations from a configuration file. 
    
    The first, optional argument (init) may be a pre-loaded type environment. 
    Use this when first loading a global configuration file before loading a 
    local one. Local definitions will shadow global ones. 

    The second argument is the string representation of the configuration file.
    *)
    val load_annotations_json : ?init:typequals -> string -> typequals

    val load_annotations_yaml : ?init:typequals -> string -> typequals

    (** Updates the cardinality for the input environment. *)
    val update_cardinality : cardinality -> config ->  config

    (** Updates the codomain for the input environment. *)
    val update_codomain : basetype -> config -> config  

    (** Updates the domain for the input environment. *)
    val update_domain : domain -> config -> config 

    (** Updates the dynamism for the input environment. *)
    val update_dynamism : dynamism -> config ->  config 

    (** Updates the randomness for the input envrionment. *)
    val update_randomness : randomness -> config ->  config 

    (** Updates the randomness for the input envrionment. *)
    val update_correlation : corr_t -> config ->  config 

    (** Add an empty entry in the environment for the input string. *)
    val add_default : string -> typequals -> typequals

    (** Returns the associated configuration for the input variable from the 
    environment
    *)
    val get_config : string -> typequals -> config

    (** Updates the config associated with a particular name. *)
    val update_config : string -> config -> typequals -> typequals

    (** Returns the empty environment. *)
    val empty : typequals

    (** Checks whether the input variable name has qualifier `randomness`. If 
    the value does not exist in the environment, returns false.
    *)
    val is_random : string -> typequals -> bool

    (** Returns the codomain of the input name. If the name does not exist in 
    the environment, it returns None. *)
    val get_codomain : string -> typequals -> basetype option

    (** Returns the cardinality of the input name. If the name does not exist 
    in the environment, it returns None. *)
    val get_cardinality : string -> typequals -> cardinality option 

    (** Returns the argument key for the unit of randomization. If the name 
    does not exist in the environment, it returns None.*)
    val get_unit : string -> typequals -> string option 

    val string_of_typequals : typequals -> string
    val string_of_config : config -> string
end

(** Auxiliary functor for creating a custom Config module from an input 
basetype specification 
*)
module Make (Cfg : Config_lang) : Config 
    with type basetype = Cfg.basetype
