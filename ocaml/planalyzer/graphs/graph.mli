(** The input struct for creating various instances of graphs. *)
module type Graph_type = sig
    (** The type of the map lookup. *)
    type key [@@deriving show]
    
    (** The type for the input program. *)
    type program [@@deriving show]

    (** Function for computing the order on two input keys. *)
    val key_compare : key -> key -> int 

    (** Function to convert a key to a string. *)
    val key_to_str : key -> string 

    (** Function to extract all variables from an input program. This is used 
    to initialize the graph. *)
    val get_program_variables : program -> key list 
end 

(** The (abstract) base signature returned by the Make functor. *)
module type Graph = sig

    (** The type of the graph key. This will be the same as in Graph_type. *)
    type key

    (** The type of the input program. This will be the same as in Graph_type. *)
    type program

    (** The type signature for the whole graph. *)
    type outer 

    (** The type signature for a row in the graph. *)
    type inner 

    exception GraphError of key * outer

    (** Function that takes a graph and returns a list of all its node names. *)
    val nodes : outer -> key list

    (** Function that takes a graph and returns a list of all the directed 
    edges. The first entry in tuple returned is the from node; the second is 
    the to node. *)
    val edges : outer -> (key * key) list

    (** Sets the input graph's value at the (from_node, to_node) location. *)
    val set : outer -> from_node:key -> to_node:key -> int -> outer

    (** Returns the value at the input graph's nodes. Equivalent to a query on 
    the edge between two nodes; can be interpreted as existence, direction, 
    etc. *)
    val get : outer -> from_node:key -> to_node:key -> int

    (** Removes a key from the input graph. *)
    val remove : outer -> key -> outer

    val string_of_graph : ?max_len:int -> outer -> string 

    (** Tests whether the supplied key has no ancestors in the input graph. *)
    val is_root : key -> outer -> bool

    (** Tests whether the supplied key has no descendants in the input graph. *)
    val is_leaf : key -> outer -> bool

    (** Returns a list of the nodes having no ancestors. *)
    val get_roots : outer -> key list

    (** Returns a list of the nodes having no descendants. *)
    val get_leaves : outer -> key list

    (** Returns a list of all the nodes having directed edges that start from 
    the input node, given the input graph. *)
    val get_children : outer -> key -> key list 

    (** Returns a list of all the nodes having directed edges that end at the 
    input node, given the input graph. *)
    val get_parents : outer -> key -> key list 

    (** Returns all of the nodes lying on directed paths that end at the input 
    node, given the input graph. *)
    val get_ancestors : ?exclude:(key list) -> outer -> key -> key list

    (** Returns all of the nodes lying on directed paths that start at the 
    input node, given the input graph. *)
    val get_descendants : ?exclude:(key list) -> outer -> key -> key list 

    (** Returns an empty adjacency matrix (i.e. graph) whose nodes/keys 
    correspond to all variables defined or used in the input program. *)
    val initialize_adjacency_matrix : key list -> outer 

    (** Returns a toplogical sort of the keys/nodes for the input grpah. Note 
    that there is no guaranteed order for nodes in an equivalence class. *)
    val topological_sort : outer -> key list 

    (** For an input key, collapse all paths through node. e.g., for some graph 
    A --> B --> C, if we remove B, we are left with A --> C. *)
    val collapse_node : key -> outer -> outer 
end

(** Functor to gcreate a Graph module from an input Graph_type struct. *)
module Make (Gtype : Graph_type) : Graph 
    with type key = Gtype.key
    and type program = Gtype.program