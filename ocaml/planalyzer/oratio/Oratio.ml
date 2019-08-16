exception ConversionError of string 
exception BadArgError
exception BadDomainError of string

let maxcalls = 10

type ratio =
  | Ratio of int * int
  | ReducedRatio of int * int
[@@deriving show]

type decimal =
  | Decimal of int * int * int

type integer =
  | Integer of int

type sciNot =
  | ScientificNotation of ratio * int 

type numbers =
  | R of ratio
  | D of decimal
  | I of integer
  | S of sciNot 

let zero = ReducedRatio (0, 1)
let one = ReducedRatio (1, 1)
let neg_one = ReducedRatio (-1, 1)

(* Conversion between ratio and base types *)
let float_of_ratio (r : ratio) : float = match r with 
  | Ratio (n, d)
  | ReducedRatio (n, d) ->
      (float_of_int n) /. (float_of_int d)

let ratio_of_int (i : int) : ratio = ReducedRatio (i, 1)

(* Some helper functions *)
let rec int_pow (base: int) (power: int) : int =
  if abs power < 1 && power > 0
  then raise (BadDomainError "Cannot compute roots.")
  else if power < 0
  then raise (BadDomainError "Function must return int, not ratio")
  else
    begin
      match power with
      | 0 -> 1
      | 1 -> base
      | _ -> base * (int_pow base (power - 1))
    end

let get_width n =
  let rec helper width =
    match n with
    | 0 -> 0
    | n' when n' < (int_pow 10 width) -> 1
    | _ -> 1 + (helper (width + 1)) in
  helper 1

let rec gcd a b =
  match (a mod b) with
    0 -> b
  | r -> gcd b r

(* Conversion between ratio and other numbers types. *)

let rec ratio_of_scinot s : ratio =
  match s with
  | ScientificNotation(mantissa, exp) -> 
    let op = match exp with 
      | 0 -> fun a _ -> a 
      | n when n > 0 -> multiply ~reduce:true
      | _ -> divide in 
    let arg = abs exp |> int_pow 10 |> ratio_of_int in 
    op mantissa arg 
and multiply ?(reduce=true) r1 r2 = match reduce_ratio r1, reduce_ratio r2 with
  | ReducedRatio (n1, d1), ReducedRatio (n2, d2) ->
     let r = Ratio (n1 * n2, d1 * d2) in
     if reduce then reduce_ratio r else r
  | _ -> raise (ConversionError "results not reduced")
and divide r1 r2 = match r2 with
  | Ratio (n, d) | ReducedRatio (n, d) -> multiply r1 (Ratio (d, n))
and reduce_ratio ?(numcalls=0) = function
  | ReducedRatio _ as r -> r
  | Ratio (n, d) ->
     if numcalls > maxcalls
     then Ratio (n, d)
     else
       begin
         let base = gcd n d in
         let numerator = n / base in
         let denominator = d / base in
         ReducedRatio (numerator, denominator)
       end
and ratio_of_decimal = function
  | Decimal (n1, n2, times) ->
   let width = get_width n2 + times in
   let d2 = int_pow 10 width in
   (* Printf.printf "n1: %d\tn2: %d\ttimes: %d\twidth: %d\td2: %d\n" n1 n2 times width d2; *)
   if n1 == 0
   then Ratio(n2, d2) 
   else add (Ratio(n1, 1)) (Ratio(n2, d2))
and add ?(reduce=true) r1 r2 =
  let r1' = reduce_ratio r1 in
  let r2' = reduce_ratio r2 in
  match r1', r2' with
  | ReducedRatio (n1, d1), ReducedRatio (n2, d2) ->
     let sum = if d1 <> d2
         then Ratio (((n1 * d2) + (n2 * d1)), (d1 * d2))
         else Ratio (n1 + n2, d1) in
     if reduce then reduce_ratio sum else sum
  | _ -> raise (ConversionError "results not reduced")
    
let string_of_ratio (r : ratio) : string =
  match r with
  | Ratio(n, 1) | ReducedRatio (n, 1) -> string_of_int n
  | Ratio(n,d) -> (string_of_int n) ^ "/" ^ (string_of_int d)
  | ReducedRatio(n,d) ->  (string_of_int n) ^ "/" ^ (string_of_int d)

let string_of_decimal (d : decimal) : string = 
  ratio_of_decimal d |> float_of_ratio |> Printf.sprintf "%f"

let string_of_integer (Integer i) : string = Printf.sprintf "%d" i 

let string_of_scinot (s : sciNot) : string = 
  ratio_of_scinot s |> float_of_ratio |> Printf.sprintf "%f" 

let string_of_number (n : numbers) = match n with 
  | R r -> string_of_ratio r
  | D d -> string_of_decimal d
  | I i -> string_of_integer i 
  | S s -> string_of_scinot s

let rec check_prime n prev_primes =
  match prev_primes with
  | [] -> true
  | h::t -> (match (n mod h) with
	     | 0 -> false
	     | _ -> check_prime n t)

let rec next_prime (n: int) (prev_primes: int list): int =
  if (check_prime (n + 1) prev_primes)
  then n + 1
  else next_prime (n + 1) prev_primes

let rec is_prime n =
  let rec get_prev_primes (n' : int) (lst : int list) =
    match (n' == abs(n), check_prime n' lst) with
    | (true, true) -> n'::lst
    | (true, false) -> lst
    | (false, true) -> get_prev_primes (n' + 1) (n'::lst)
    | (false, false) -> get_prev_primes (n' + 1) lst
  in
  match n with
  | 0 | 1 -> false
  | _ -> (match get_prev_primes 2 [2] with
	   | h::t when h == abs(n) -> true
	   | _ -> false)

let nats i = Stream.from (fun j -> Some (i + j));;
			 
let primes nums =
  let rec next n =
    match (Stream.next nums) with
    | n' -> if (is_prime n')
	    then Some n'
	    else next n
  in
  Stream.from next;;

let new_prime_stream () =
  primes (nats 1);;

let factor_by n f : (int * int) =
  let rec helper r p =
    match (r, (r mod f)) with
    | (0, 0) -> (r, p)
    | (_, 0) -> helper (r / f) (p + 1)
    | (_, _) -> (r, p)
  in
  helper n 0;;

  
let greatest_multiple_factor n d p =
   let (n, m1) = factor_by n p in
   let (d, m2) = factor_by d p in
   int_pow p (min m1 m2)
  
let subtract r1 r2 =
  let r1' = reduce_ratio r1 in
  let r2' = reduce_ratio r2 in
  match r1', r2' with
  | ReducedRatio (n1, d1), ReducedRatio (n2, d2) ->
     reduce_ratio ~numcalls:1 (Ratio (((n1 * d2) - (n2 * d1)), (d1 * d2)))
  | _ -> raise (ConversionError "results not reduced")

let int_of_ratio r =
  let r' = reduce_ratio r in
  match r' with
  | ReducedRatio (n, d) -> n / d
  | _ -> raise (ConversionError "results not reduced")
  
let rec equals r1 r2 =
  let r1' = reduce_ratio r1 in
  let r2' = reduce_ratio r2 in
  match r1', r2' with
  | ReducedRatio (n1, d1), ReducedRatio (n2, d2) -> n1 == n2 && d1 == d2
  | _ -> raise (ConversionError "results not reduced")

let rec lt r1 r2 = match r1, r2 with
  | ReducedRatio (n1, d1), ReducedRatio (n2, d2)
  | ReducedRatio (n1, d1), Ratio (n2, d2)
  | Ratio (n1, d1), ReducedRatio (n2, d2)
  | Ratio (n1, d1), Ratio (n2, d2) ->
     let n1' = float_of_int n1 in
     let d1' = float_of_int d1 in
     let n2' = float_of_int n2 in
     let d2' = float_of_int d2 in
     (n1' /. d1') < (n2' /. d2')

let rec gt r1 r2 = lt r2 r1
 
and convert_to_reduced_ratio = function
  | R r ->
     begin
       match r with
       | ReducedRatio _ -> r
       | Ratio _ -> reduce_ratio r
     end 
  | D d ->
     let r = ratio_of_decimal d in
     reduce_ratio r 
    (* r *)
  | I (Integer i) -> ReducedRatio(i, 1)
  | S s -> reduce_ratio (ratio_of_scinot s)
and ratio_of_float f ast =
  let split_on_exp = string_of_float f |> Str.split (Str.regexp "e") in
  let split_on_decimal = string_of_float f |> Str.split (Str.regexp "\\.") in
  (* Printf.printf "ratio_of_float: %0.20f\n#/split_on_exp: %d\t#/split_on_decimal: %d\n" f (List.length split_on_exp) (List.length split_on_decimal); *)
  if List.length split_on_exp > 1
  then
    begin match split_on_exp with
      | [mantissa ; exp] ->
        begin try
          let left = ratio_of_float (float_of_string mantissa) ast in 
          let right = int_of_string exp in 
          (* Printf.printf "left: %s\tright: %d\n" (string_of_ratio left) right; *)
          S (ScientificNotation (left, right))
        with Failure msg when msg = "int_of_string" ->
          raise (ConversionError (Printf.sprintf "Could not convert %f to scientific notation" f))
        end 
	      |> convert_to_reduced_ratio
      | _ -> raise (ConversionError 
        (Printf.sprintf "Could not convert %f to scientific notation" f))
    end
  else
   begin match split_on_decimal with
      | [lradix; rradix] ->
	      let zerorxp = Str.regexp "0+" in
	      let num_zeros = (try
			       ignore (Str.search_backward zerorxp rradix 0);
			       Str.matched_string rradix |> String.length
			     with Not_found -> 0) in
        (* Printf.printf "lradix: %s\trradix: %s\tnumzeros: %d\n" lradix rradix num_zeros; *)
        D (Decimal (int_of_string lradix, int_of_string rradix, num_zeros))
	      |> convert_to_reduced_ratio
      | _ -> raise (ConversionError 
        (Printf.sprintf "Could not convert %f to decimal" f))
    end
and ratio_of_num_et_den n d =
  convert_to_reduced_ratio (R (Ratio (n, d)))
    

let modulus r1 r2 =
  match r1, r2 with 
  | ReducedRatio (n1, 1), ReducedRatio (n2, 1)
  | Ratio (n1, 1), Ratio (n2, 1) ->
    ReducedRatio (n1 mod n2, 1)
  | _ -> raise (BadDomainError (Printf.sprintf 
    "Modulus on non-integers not supported (%s %% %s)" 
    (string_of_ratio r1)
    (string_of_ratio r2)))

let normalize (lst : ratio list) =
  (* Group by denominator *)
  (* Doing this by groups because the naive implementation hangs when there are
      too many conditions -- This is because integer factorization is in NP.*)
  (* Heuristic: if any of the weights are greater than 1, then normalize *)
  if lst
     |> List.filter (fun o -> match o with 
                     | Ratio (n,d) 
                     | ReducedRatio (n,d) ->
	                      (float_of_int n) /. (float_of_int d) > 1.0)
     |> List.length
     |> (==) 0
  then lst
  else
    begin
      let groups = List.fold_left (fun gs n ->
		       match n with
		       | Ratio (_, d) | ReducedRatio (_, d) ->
			  let dlist = try List.assoc d gs with Not_found -> [] in
			  let swap = List.remove_assoc d gs in
			  (d, n::dlist)::swap)
				  [] lst in
      let num_groups = List.length groups in
      let max_group_len : int = List.map snd groups (* should be a list of lists *)
				|> List.map List.length (* should be a list of nums *)
				|> List.fold_left max 0 in
      let max_denom : int = List.map fst groups |> List.fold_left max 0 in
      let reducep : bool = ((num_groups < 10) &&
			      (max_group_len < 10) &&
				(max_denom < 10000)) in
      let add' = if reducep then add ~reduce:true else add ~reduce:false in
      let lst' = List.map (fun nlst -> List.fold_left add' (ratio_of_int 0) nlst)
			  (groups |> List.map snd) in
      let n = List.fold_left add' (ratio_of_int 0) lst' in
      List.map (fun i -> divide i n) lst
    end
