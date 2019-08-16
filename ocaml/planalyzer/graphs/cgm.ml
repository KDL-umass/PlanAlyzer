module type Cgm = sig
  include Graph.Graph
  type path 
  val build_causal_graphs : path list -> outer list
end

module Make(In: sig 
    include Graph.Graph_type
    type path 
    val output_var : key 
    val find_dependents : path -> key -> key list
    val get_path_variables : path -> key list 
  end) : Cgm with type key = In.key and type path = In.path = struct
    
    module M = Graph.Make(In)
    include M     
    type path = In.path 

    let output_var = In.output_var 

    let build_causal_graph (path : In.path) : outer = 
      let keys = In.get_path_variables path in 
      let empty = initialize_adjacency_matrix (output_var::keys) in 
      let deps = List.map (In.find_dependents path) keys in 
      let pairs = List.combine keys deps 
                  |> List.map (fun (k, lst) -> (k, output_var::lst)) in 
      List.fold_left (fun (g : outer) ((from : key), (tos : key list)) ->
        let fn g k = set g from k 1 in 
        List.fold_left fn g tos
        ) empty ((output_var, [])::pairs)

    let build_causal_graphs (program : In.path list) : outer list = 
      List.map build_causal_graph program 

  end