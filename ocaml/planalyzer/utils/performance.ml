open Logging 
open Sexplib.Std

let timing = ref []
let current_phase : phase option ref = ref None 

let time ?(fname="") phase fn = 
  current_phase := Some phase;
  let t1 = Unix.gettimeofday () in 
  let res = fn () in 
  let t2 = Unix.gettimeofday () in 
  timing := (phase, fname, t2 -. t1)::(!timing);
  current_phase := None;
  res 

let report () : string = 
  let open Printf in 
  let finished = Utils.join 
    "\n"
    (fun (p, f, t) -> sprintf "%s:%s %fs" (sexp_of_phase p |> string_of_sexp) f t)
    (List.rev !timing) in 
  let terminated = match !current_phase with 
    | None -> ""
    | Some phase -> phase
      |> sexp_of_phase 
      |> string_of_sexp
      |> sprintf "\nTerminated in phase %s" in 
  finished ^ terminated ^ "\n"