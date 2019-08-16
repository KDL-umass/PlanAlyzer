(** The counters modules contains all counter-related functionality. This is 
useful for SSA-ifying variables, generating fresh variables, etc. The counters 
here are stateful; tests run using these may need to be run with the 
`-runner sequential` option in OUnit (or use a non-stateful mock, which is not 
currently implemented). *)

(** Returns a new counter with prefix "skip", used in the Skip AST node. *)
val skipid : unit -> string

(** Returns a new fresh variable id. *)
val varid : unit -> string

(** A unique prefix for fresh variables, like a gensym. Default: (^fvid). 
    Note that PlanOut variables may not begin with the ^ character, so there 
    should be no name clashes. Also note that Z3 requires variable names to be 
    ASCII so this restricts e.g. non-visible whitespace options. *)
val pseudo_prefix : string 

(** Resets the input counter name to zero. *)
val renew_uid : string -> unit 

val thread_safe_copy : ?prefix:string -> string -> unit -> string 