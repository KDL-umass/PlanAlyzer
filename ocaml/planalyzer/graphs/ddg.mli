module type Graph_type = sig
  include Graph.Graph_type
  val find_dependents : program -> key -> key list 
end 

module type Ddg = sig
    include Graph.Graph
    val build_dependence_graph : program -> outer
end

module Make(Gtype : Graph_type) : Ddg
  with type key = Gtype.key 
  and type program = Gtype.program 