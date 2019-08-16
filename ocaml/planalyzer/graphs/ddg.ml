module type Graph_type = sig
    include Graph.Graph_type
    val find_dependents : program -> key -> key list 
end 

module type Ddg = sig
    include Graph.Graph
    val build_dependence_graph : program -> outer
end

module Make(Gtype : Graph_type) = struct

    module M = Graph.Make(Gtype)
    include M 
    let build_dependence_graph program : outer =
      let keys = Gtype.get_program_variables program in 
      let empty = initialize_adjacency_matrix keys in
      let deps = List.map (Gtype.find_dependents program) keys in 
      let pairs = List.combine keys deps in 
      List.fold_left (fun (g : outer) ((from : key), (tos : key list)) ->
        let fn g k = set g from k 1 in 
        List.fold_left fn g tos
        ) empty pairs
end
