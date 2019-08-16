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
  end) : Cgm with type key = In.key and type path = In.path