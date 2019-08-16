type phase = 
  | All 
  | Transform 
  | Normalize 
  | Ddg 
  | Corepo 
  | Semantics 
  | Estimators 
[@@deriving sexp, show]

let all_phases = [All; Transform; Normalize; Ddg; Corepo; Semantics; Estimators] 

let registered_loggers : phase list ref = ref [] 

let get_registered_loggers _ = !registered_loggers

let turn_off phase : unit = 
  registered_loggers := !registered_loggers
    |> List.filter (fun p -> p <> phase)

let turn_on phase : unit = 
  if not (List.mem phase !registered_loggers)
  then registered_loggers := phase::!registered_loggers

module Make (In: sig 
    val file : string 
    val phase : phase 
end) = struct
    
    let on _ = 
      List.mem In.phase !registered_loggers 
  
    let print_debug linno fmt =
      if on () then 
        Log.debug ("\027[1;36m[%s:%d] " ^^ fmt ^^ "\027[0m") 
          In.file linno
      else Printf.ifprintf stderr fmt 
  
    let print_warn linno fmt =
      if on ()  then 
        Log.warn ("\027[1;31m[%s:%d] " ^^ fmt ^^ "\027[0m\n") 
          In.file linno
      else Printf.ifprintf stderr fmt
    
    let print_info linno fmt = 
      if on ()  then 
        Log.info ("\027[1;34m[%s:%d] " ^^ fmt ^^ "\027[0m\n")
         In.file linno
      else Printf.ifprintf stdout fmt
end