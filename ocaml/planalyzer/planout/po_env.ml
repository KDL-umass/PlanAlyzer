(** Dependencies:
    - config 
    - po_syntax
*)
(********************************************************************************
  This module handles the execution environment for PlanOut variables. The
  environment holds partially-evaluated expressions. All variables are indexed 
  by their name and index (from SSA). A separate map holds origin information 
  (i.e., whether a variable is synthetic or from the source file.)

  All variables are assigned their SSA values during parsing, which is depth-
  first. 
*******************************************************************************)
open Printf
open Po_syntax
open Sexplib.Conv
open Config 

(** The key to look up variables in the environment. *)
type env_key = string * int 

let string_of_origin _ = ""

(** This module tracks current expressions/values associated with indexed 
variables, and the variable sources (i.e., synthetic or in the source file) *)
module Env = struct 

  (** The typical *)
  module Delta = Map.Make(
		 struct
		   type t = env_key
		   let compare (p1 : t) (p2 : t) = match p1, p2 with 
       | (name1, index1), (name2, index2) ->
          begin match compare name1 name2 with
            | 0 -> compare index1 index2 
            | cmp -> cmp  
           end
        end) 

  module Sources = Map.Make(String)

  let add ?(o=SrcUnknown) k v (delta, sources) = 
    let (s, _) = k in 
    (* if o = ExtSource then assert false; *)
    let o' = if Sources.mem s sources 
             then match Sources.find s sources with 
             | SrcUnknown -> o
             (* | ExtSource -> assert false *)
             | o' -> o'                
             else o in 
    (Delta.add k v delta, Sources.add s o' sources)

  let find k (delta, _) : po_expr = 
    try
      Delta.find k delta
    with Not_found -> 
      Printf.printf "\nKey (%s, %d) not found\n" (fst k) (snd k);
      raise Not_found

  let equivs s (delta, _) : env_key list = 
    Delta.bindings delta
    |> List.map fst
    |> List.filter (fun (s', _) -> s = s')

  end

(** The type of the environment *)
type env = po_expr Env.Delta.t * origin Env.Sources.t

(** Add a key and value (and optionally an origin) to the environment. *)
let add = Env.add

(** Look up the expression associated with a key in the environment. *)
let find = Env.find 		    

(** Tries to return the resulting expression as a container. *)
let find_container k env : po_cexpr = to_container (Env.find k env)

(** Return an empty environment. *)
let empty = (Env.Delta.empty, Env.Sources.empty)

(** Test whether the input key has already been added to the environment. *)
let mem k (delta, _) = Env.Delta.mem k delta 

(** Get all of the bindings in the environment. *)
let bindings (delta, _) : (env_key * po_expr) list = Env.Delta.bindings delta
	  
(** Find the maximum (SSA) index associated with the input variable name. *)    
let env_find_max_index (s : string) env = 
  Env.equivs s env 
  |> List.map snd
  |> List.fold_left max 0

(** Get the latest indexed variable and the value to which it's bound. *)
let env_find_latest_binding env (s : string) = 
  let i = env_find_max_index s env in 
  let k = (s, i) in 
  (k, find k env)

(** Find the mode type associated with the input key. *)
let rec env_find_mode k env =
  let (s, i) = k in 
  if i = 0
  then External
  else match find (s, i) env with 
    | CustomExpr (_, _, Some _)
    | Aexpr (RandomNumber _)
    | Aexpr (CustomNumber (_, _, Some _))
    | Bexpr (RandomBoolean _)
    | Bexpr (CustomBoolean (_, _, Some _))
    | Cexpr (RandomContainer _)
    | Cexpr (CustomContainer (_, _, _, Some _))
    | Sexpr (RandomString _) 
    | Sexpr (CustomString (_, _, Some _))
      -> Random
    | Get (_, m, _, _) -> m
    | _ -> Unclassified

let string_of_env (type t) (tgt_fn : t -> string) (delta, sources) =
  Env.Delta.bindings delta
  |> List.map (fun (label, value) -> (label, tgt_fn value))
  |> List.map (fun ((k, i), v) ->
      let o = Env.Sources.find k sources in 
      if i > 0
      then sprintf "(%s, %d, %s) => %s" k i (string_of_origin o) v
      else sprintf "%s => %s" k v)
  |> Core.String.concat ~sep:",\n\t" 
  |> Printf.sprintf "Env{\n\t%s\n}"

(** Reset the value of the variable having the highest index to the input 
value. *)
let env_update_latest s v env =
  (* Updates the latest *)
  add (s, env_find_max_index s env) v env

(** The merge function for merging two environments; we assume that the first 
has priority over the second. *)
let env_merge_fn k a b = 
  match a, b with
  | Some a', Some b' when not (a' = b') -> assert false
  | Some a', _ -> Some a'
  | None, Some b' -> Some b'
  | _ -> None

(** Merges two environments. *)
let merge_env ((d1, s1) : env) ((d2, s2) : env) : env = 
  (Env.Delta.merge env_merge_fn d1 d2, Env.Sources.merge env_merge_fn s1 s2)

(** Produces a subset environment only of those bindings that satisfy the input 
predicate. *)
let env_extract (fn : 't -> bool) env =
  Env.Delta.bindings env
  |> List.filter (fun (k, v) -> fn v)

(** Returns the origin for the input (non-indexed) variable name. *)
let get_origin s (_, sources) : origin = 
  if Env.Sources.mem s sources
  then Env.Sources.find s sources
  else ExtSource

(** Checks whether the input variable name is a synthetic one. *)
let is_pseudo_var env name = 
  get_origin name env = Synth

(** Returns the bindings of the max indices of all variables. *)
let env_latest_bindings (delta, sources) =
  Env.Sources.bindings sources 
  |> List.map fst
  |> List.map (env_find_latest_binding (delta, sources))
  

(** Finalizes the environment; sets all values to be the values at their max 
indices and resets all indices to 0. *)
(* let env_consolidate env =
  let (delta, sources) = env in 
  Env.Delta.bindings delta
  |> List.map fst 
  |> List.fold_left (fun env' (s, i) ->
                    let i' = env_find_max_index s env in
                    let e = find (s, i') env in
                    Env.add (s, 0) e env') 
      (Env.Delta.empty, sources) *)
    

(** Populates the environment for the input path. *)
let rec populate_env_for_path ?(env=empty) = function
  | [] -> env
  | h::t -> populate_env_for_path ~env:(match h with
                                        | Assignment (origin, label, i, e) -> 
                                          add ~o:origin (label, i) e env
                                        | _ -> env)
                                  t

(** Returns all bindings for a name (i.e., all versions of a label's name in 
this environment). *)
let env_bindings_for_name env s =
  Env.equivs s env
  |> List.map (fun k -> (k, find k env))

(** Returns all bindings that have a label name in the input list of names. *)
let env_bindings_subset_for_names names env =
  List.map (env_bindings_for_name env) names
  |> List.flatten
  |> List.filter (fun ((s, _), _) -> List.mem s names) 

(** Returns an environment that has all bindings whose names are in the input 
list of names. *)
let env_subset_for_names ?(ignore_pseudo=true) names env =
  env_bindings_subset_for_names names env
  |> List.filter (fun ((k, _), _) -> 
                  if ignore_pseudo then not (is_pseudo_var env k) else true)
  |> List.fold_left (fun e (k, v) -> Env.add k v e) empty

(** Checks whether the first argument is a subset of the second. *)
let is_env_subset ?(ignore_pseudo=true) env_sub env =
  List.for_all (fun ((k : env_key), (v : po_expr)) ->
                if ignore_pseudo && (is_pseudo_var env (fst k))
                then true
                else mem k env && find k env = v)
               (Env.Delta.bindings env_sub)

(** Checks whether input name has been defined so far. *)
let has_name (_, sources) name =
  Env.Sources.mem name sources

(** Checks whether the set of names are all in the environment. *)  
let is_env_subset_names ?(ignore_pseudo=true) env names  =
  List.for_all (has_name env) 
               (if ignore_pseudo 
               then (List.filter (fun x -> not (is_pseudo_var env x)) names) 
               else names)
                         
(** Infers the expression type from AST structure alone. This function does not 
use type annotations; types must already have been translated to the 
appropriate syntactical tag (constructor). No inference happens here. *)
let get_expression_type (e : po_expr) = match e with 
| Aexpr _ -> Number
| Bexpr _ -> Boolean
| Cexpr _ -> Container
| Sexpr _ -> String
| _ -> Unknown