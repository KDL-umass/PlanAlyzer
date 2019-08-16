open Printf

let rec join (sep: string) (convert: 'a -> string) (lst : 'a list) =
  String.concat sep (List.map convert lst)

let rec extend_paths (from_paths : 'a list list) (to_paths: 'a list list) : 'a list list =
  match from_paths with
  | [] -> []
  | hfrom::tfrom -> let rec extend_paths_helper tpaths =
		      match tpaths with
		      | [] -> []
		      | hto::tto -> (hfrom @ hto)::(extend_paths_helper tto)
		    in
		    (extend_paths_helper to_paths) @ (extend_paths tfrom to_paths)

let ffirst ?(outer_empty_msg:string = "Outer Empty")
	   ?(inner_empty_msg:string = "Inner Empty")
	   ?(outer_long_msg:string = "Nondeterminism and/or branching not allowed.")
	   ?(inner_long_msg:string = "Complex expressions not allowed.")
	   (f : 'a -> 'b list list) a =
  match f a with
  | [[ foo ]] -> foo
  | [] -> failwith outer_empty_msg
  | [[]] -> failwith inner_empty_msg
  | h::t -> failwith outer_long_msg

let identity i =  i

exception ItemNotFoundException
exception IndexOutOfBoundsException
		    
let rec index_of (lst : 'a list) (item: 'a) : int =
  match lst with
  | [] -> raise ItemNotFoundException
  | h::t when h <> item -> 1 + index_of t item
  | _ -> 0
		    

let rec replace (lst: 'a list) (index: int) (item: 'a) : 'a list =
  match index, lst with
  | -1, _ -> lst @ [item]
  | 0, _::t -> item::t
  | n, h::t -> h::(replace t index item)
  | _, [] -> raise IndexOutOfBoundsException


let uniq (lst : 'a list) : 'a list  =
  let rec helper (m  : 'a list) = function
    | [] -> m
    | h::t ->
       if List.mem h m
       then helper m t
       else helper (h::m) t in
  helper [] lst


let rec range int : int list =
  match int with
  | 0 -> []
  | n when n < 0
    -> failwith (sprintf "Cannot compute range on a negative number: %d" n)
  | n -> n-1::range (n - 1)
  
let rec enumerate (type a) (lst : a list) : (int * a) list =
  let ids = range (List.length lst) in 
  assert ((List.length ids) = (List.length lst));
  List.combine (List.rev ids) lst

let replace (lst : 'a list) (i : int) (e : 'a) : 'a list =
  let ilst = enumerate lst in
  let lhs = List.filter (fun (i', _) -> i' < i) ilst |> List.map snd in
  let rhs = List.filter (fun (i', _) -> i' > i) ilst |> List.map snd in
  lhs @ [ e ] @ rhs

let not_fn (fn : 'a -> bool) a =
  not (fn a)

(* Things that otherwise would belong in extlib, which may not be accessible via js_of_ocaml *)
let is_none = function
  | None -> true
  | _ -> false

let extract = function 
  | Some s -> s
  | _ -> failwith "Not expecting None here."

let match_arg a = function
  | Some b -> compare a b == 0
  | _ -> false

(* There is a List.for_all, but no List.exists? Wrapping both in more Python-esque names. *)
let all fn lst =
  List.for_all fn lst
	       
let exists fn lst =
  not (all (not_fn fn) lst)

let string_from_file fname =
  let str_file = ref "" in
  let f = open_in fname in
  begin
    try 
      while true do
	      str_file := !str_file ^ input_line f 
      done;
    with End_of_file -> close_in_noerr f
  end;
  !str_file 

let string_to_file (fname : string) (str : string) : unit = 
  let f = open_out fname in 
  try 
    output_string f str
  with End_of_file -> close_out_noerr f

let mkdir dirname =
  try
   Unix.mkdir dirname 0o755
  with Unix.Unix_error (code, _, _) when code = Unix.EEXIST -> ()

let split3 l = 
  List.fold_right (fun (a, b, c) (a_list, b_list, c_list) ->
    (a::a_list, b::b_list, c::c_list))
    l
    ([], [], [])
    

let rec combine3 l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | h1::t1, h2::t2, h3::t3 -> (h1, h2, h3)::(combine3 t1 t2 t3)
  | _ -> failwith "Unequal list arguments to combine3"

let fst3 = function
  | (a, _, _) -> a

let snd3 = function
  | (_, b, _) -> b

let thd3 = function
  | (_, _, c) -> c
  

let filter_map (fn : 'a -> 'b option) (lst : 'a list) =
  List.map fn lst
  |> List.filter (fun a -> match a with Some _ -> true | None -> false)
  |> List.map (fun a -> match a with Some b -> b | _ -> assert false)


let rec take (n : int) (lst : 'a list) : 'a list = match n, lst with 
  | 0, _ | _, [] -> []
  | _, h::t -> h::(take (n - 1) t)

let asserts file linno pred msg  = 
  if not pred 
  then begin 
    Printf.printf "\027[1;35mFAILURE [%s:%d]: %s\027[0m\n]" file linno msg;
    assert false 
  end

let same = function 
  | [] -> true
  | h::t ->
     let rec same_helper = function
       | [] -> true
       | h'::t -> if h = h'
                  then same_helper t
                  else false
     in same_helper t

let remove_newlines s =
  let r = Str.regexp "\n" in
  Str.global_substitute r (fun _ -> "") s

let all_pairs (type t) (lst : t list) = 
  let retval = ref [] in 
  for i=0 to List.length lst - 1 do
    for j=(i + 1) to List.length lst - 1 do
      retval := (List.nth lst i, List.nth lst j)::!retval
    done
  done;
  !retval

let starts_with (base : string) (cmp : string) =
  Str.string_before base (String.length cmp) = cmp 

let swap_tuple (a, b) = (b, a)