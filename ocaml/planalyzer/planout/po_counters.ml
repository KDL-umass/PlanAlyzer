let (_counters : (string * int ref) list ref) = ref []

let _make_uid_fn ?(prefix="") name : unit -> string =
  let counter_id = (name, ref 0) in
  _counters := counter_id::!_counters;
  let retval _ =
    let this_counter = List.assoc name !_counters in
    incr this_counter;
    Log.debug "Incrementing counter %s to %d\n" name !this_counter; 
    prefix ^ (string_of_int !this_counter) in
  retval

let renew_uid name =
  _counters := (name, ref 0)::(List.remove_assoc name !_counters)

let pseudo_prefix = "^fvid" (* Non-ascii prefix in case of name clash. *)

let varid = _make_uid_fn ~prefix:pseudo_prefix pseudo_prefix

let labelid _ = _make_uid_fn ~prefix:"" "labelid" () |> int_of_string

let skipid = _make_uid_fn ~prefix:"" "skipid"

let thread_safe_copy ?(prefix="") name = 
  let token = string_of_float (Sys.time ()) in 
  let new_name = name ^ token in     
  let i = (if List.mem_assoc name !_counters 
          then !(List.assoc name !_counters)
          else 0) in 
  _counters := (new_name, ref i)::!_counters;
  let retval _ = 
    let this_counter = List.assoc new_name !_counters in 
    incr this_counter;
    Log.debug "Incrementing thread-safe counter %s to %d\n" 
      new_name !this_counter;
    prefix ^ (string_of_int !this_counter) in 
  retval

