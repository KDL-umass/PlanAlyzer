module type Graph_type = sig
    type key [@@deriving sexp]
    type program
    val key_compare : key -> key -> int     
    val key_to_str : key -> string 
    (* val sexp_of_key : key -> Sexplib.Sexp.t
    val key_of_sexp : Sexplib.Sexp.t -> key *)
    val get_program_variables : program -> key list 
end 

module type Graph = sig
    
    type key
    type program
    type outer 
    type inner 

    exception GraphError of key * outer

    val nodes : outer -> key list
    val edges : outer -> (key * key) list
    val set : outer -> from_node:key -> to_node:key -> int -> outer
    val get : outer -> from_node:key -> to_node:key -> int
    val remove : outer -> key -> outer
    val string_of_graph : ?max_len:int -> outer -> string 
    val is_root : key -> outer -> bool
    val is_leaf : key -> outer -> bool
    val get_roots : outer -> key list
    val get_leaves : outer -> key list
    val get_children : outer -> key -> key list 
    val get_parents : outer -> key -> key list 
    val get_ancestors : ?exclude:(key list) -> outer -> key -> key list
    val get_descendants : ?exclude:(key list) -> outer -> key -> key list 
    val initialize_adjacency_matrix : key list -> outer 
    val topological_sort : outer -> key list 
    val collapse_node : key -> outer -> outer
end

module Make (Gtype : Graph_type) = struct

  type key = Gtype.key
  type program = Gtype.program 

  module CtVec = Map.Make(struct 
    type t = Gtype.key
    let compare = Gtype.key_compare
    end)

  module AdjMat = Map.Make(struct
    type t = Gtype.key
    let compare = Gtype.key_compare
    end)

  type inner = int CtVec.t
  type outer = inner AdjMat.t 

  exception GraphError of key * outer 

  let nodes graph = AdjMat.bindings graph |> List.map fst

  let values graph = AdjMat.bindings graph |> List.map snd

  let string_of_graph ?(max_len=7) (m : outer) : string =
    let open Printf in 
    let get_n s = if max_len = (-1) then String.length s else max_len in 
    let try_to_grab_n s = try String.sub s 0 (get_n s) 
                          with Invalid_argument _ -> s in
    let key_strs = nodes m
                  |> List.map Gtype.key_to_str 
                  |> List.map try_to_grab_n in
    ignore (assert (List.for_all (fun ctvec -> 
                      CtVec.cardinal ctvec = List.length key_strs) 
                      (values m)));
    let open Core.String in
    let header = "\t" ^ (concat ~sep:"\t" key_strs) ^ "\n" in
    let make_row ((k : key), v) : string =
      let row_label = Gtype.key_to_str k |> try_to_grab_n in
      let cells = CtVec.bindings v |> List.map snd |> List.map string_of_int in 
      concat ~sep:"\t" (row_label::cells) in
    AdjMat.bindings m
    |> List.map make_row
    |> concat ~sep:"\n" 
    |> (^) header

  let get graph ~from_node:from_node ~to_node:to_node : int = 
    AdjMat.find from_node graph |> CtVec.find to_node
  
  let edges graph = 
    let keys = List.map 
                (fun n -> List.map (fun m -> (n, m)) (nodes graph)) 
                (nodes graph)
               |> List.flatten in 
    let rec helper = function 
      | [] -> []
      | (k1, k2)::t -> 
        if (get graph k1 k2) <> 0 
        then (k1, k2)::(helper t)
        else helper t
    in helper keys

  let set graph ~from_node ~to_node v =
    let outer = AdjMat.find from_node graph in 
    AdjMat.add from_node (CtVec.add to_node v outer) graph 

  let set_row graph k keys ints =
    let outer = AdjMat.find k graph in 
    let input = List.combine keys ints in 
    let inner = List.fold_left 
      (fun r (k', v) -> CtVec.add k' v r) outer input in 
    AdjMat.add k inner graph

  let remove graph k =
    let (ks, vs) = AdjMat.bindings graph |> List.split in 
    let vs' = List.map (CtVec.remove k) vs in 
    let pairs = List.combine ks vs' in 
    List.fold_left (fun g (k', v') -> AdjMat.add k' v' g) graph pairs 
    |> AdjMat.remove k

  let is_root (k : key) (m : outer) : bool = 
      AdjMat.bindings m
      |> List.map snd (* These are CtVecs. *)
      |> List.map (CtVec.find k)
      |> List.fold_left (+) 0
      |> (==) 0

  let is_leaf (k : key) (m : int CtVec.t AdjMat.t) : bool =
    List.fold_left (+) 0 (CtVec.bindings (AdjMat.find k m) |> List.map snd) == 0
                            
  let get_roots (m : int CtVec.t AdjMat.t) : key list =
    (* Roots have no incoming edges. This is what we track in AdjMat. *)
    nodes m |> List.filter (fun s -> is_root s m)

  let get_leaves m =
    (* Leaves have no outgoing edges. We need to search through each node to 
       see if our node of interest has an incoming edge to any other node. *)
    let params =   AdjMat.bindings m |> List.map fst in
    let filter_fn param = is_leaf param m in 
    List.filter filter_fn params

  let get_parents m n : key list =
    let children =  AdjMat.bindings m
                    |> List.filter (fun (child, parent_vec) -> 
                        CtVec.find n parent_vec == 1)
                    |> List.map fst in
    (* print_debug __LINE__ (sprintf "children: [%s]\n" (Utils.join "; " to_versioned children)); *)
    children
                                

  let get_children (m : outer) (n : key) : key list =
    try
      AdjMat.find n m
      |> CtVec.bindings
      |> List.filter (fun (_, ct) -> ct <> 0)
      |> List.map fst
    with Not_found -> raise (GraphError (n, m))

  let rec get_ancestors ?(exclude=[]) m n : key list =
    let parents = if List.mem n exclude then [] else get_parents m n in
    (* warn if we don't have a DAG. *)
    if not (List.for_all (fun p -> not (List.mem p exclude)) parents)
    then 
      let open Core.String in 
      Log.warn ": %d] Not a DAG; %s in exclusion list [%s]"
                __LINE__ (Gtype.key_to_str n)
                (List.filter (fun p -> List.mem p exclude) parents
                 |> List.map Gtype.key_to_str
                 |> concat ~sep:", " );
    else ();
    parents
    |> List.filter (fun parent -> not (List.mem parent exclude))
    |> List.map (get_ancestors ~exclude:(n::exclude) m)
    |> List.flatten
    |> (@) parents 

  let rec get_descendants ?(exclude=[]) m n : key list = 
    let children = if List.mem n exclude then [] else get_children m n in 
    children 
    |> List.filter (fun child -> not (List.mem child exclude))
    |> List.map (get_descendants ~exclude:(n::exclude) m)
    |> List.flatten
    |> (@) children 

  let initialize_adjacency_matrix params =
    (*Log.set_prefix " [%s" __FILE__;*)
    let retval =  List.fold_left
      (fun (m : int CtVec.t AdjMat.t) (p : key) ->
      (* Given node p, initialize count at node k to be 0. *)
      let init (m' : int CtVec.t) k = CtVec.add k 0 m' in
      (* Initialize all counts for a node p to be 0. *)
      let local : int CtVec.t = List.fold_left init CtVec.empty params in
      AdjMat.add p local m)
      AdjMat.empty
      params in 
    let n = AdjMat.cardinal retval in 
    assert (List.for_all (fun ctvec -> 
      CtVec.cardinal ctvec = n) (values retval));
    retval

        
  let topological_sort (graph : int CtVec.t AdjMat.t) : key list = 
    let roots : key list = get_roots graph in
    let rec sort_helper graph sorted_nodes = function 
      | [] -> sorted_nodes
      | h::t ->
        begin
          (* this needs to be breadth-first *)
          if List.mem h sorted_nodes
          then
            (* We have already encountered a variable with this name. *)
            sort_helper graph sorted_nodes t
          else 
            sort_helper graph (h::sorted_nodes) (t @ (get_children graph h))
        end 
    in sort_helper graph [] roots

    let collapse_node (k : key) (graph : outer) = 
      let in_edges = get_parents graph k in 
      let out_edges = get_children graph k in 
      let new_edges = List.fold_left (fun lst from_n ->
          lst @ (List.map (fun to_n -> (from_n, to_n)) out_edges)
        ) [] in_edges in 
      List.fold_left (fun g (in_n, out_n) -> 
        set g ~from_node:in_n ~to_node:out_n 1) (remove graph k) new_edges

end