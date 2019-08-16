open OUnit2
open Oratio

  
(* ORatio.check_prime *)

let test_prime_prime text_ctxt =
  assert_bool "2 is prime" (check_prime 2 [])

let test_prime_not_prime test_ctxt =
  assert_bool "4 is not prime" (not (check_prime 4 [2;3]))

	      
(* Oratio.next_prime *)
	      
let test_next_prime_base test_ctxt =
  assert_equal (next_prime 1 []) 2

let test_next_prime_ind test_ctxt =
  assert_equal (next_prime (next_prime (next_prime 1 []) [2]) [2;3]) 5

let test_is_prime_10 test_ctxt =
  assert_bool "10 is not prime" (not (is_prime 10))

let test_is_prime_11 test_ctxt =
  assert_bool "11 is prime" (is_prime 11)

(* Oratio.reduce_ratio *)

let test_reduce_ratio test_ctxt =
  assert_equal (reduce_ratio (ReducedRatio(1, 3))) (ReducedRatio(1,3));
  assert_equal (reduce_ratio (Ratio(1, 3))) (ReducedRatio(1,3));
  assert_equal (reduce_ratio (Ratio(9, 27))) (ReducedRatio(1,3))

(* Oratio.convert_to_reduced_ratio *)

let test_reduce_R c =
  assert_equal (convert_to_reduced_ratio (R (Ratio (60, 12)))) (ReducedRatio (5, 1))

let test_reduce_I c = 
  assert_equal (convert_to_reduced_ratio (I (Integer 10))) (ReducedRatio (10, 1))

let test_reduce_D c =
  let is = convert_to_reduced_ratio (D (Decimal (12, 5, 0))) in
  let should_be = ReducedRatio (25, 2) in
  assert_equal is should_be

let test_reduce_S c =
  assert_equal (convert_to_reduced_ratio 
    (S (ScientificNotation (ratio_of_int 4, 2)))) 
    (ReducedRatio (400, 1));
  assert_equal (convert_to_reduced_ratio 
    (S (ScientificNotation (ratio_of_int 4, (-2))))) 
    (ReducedRatio (1, 25))

let test_ratio_decimal c =
  let is = convert_to_reduced_ratio (D (Decimal (0, 234, 0))) in
  let should_be = ReducedRatio (117, 500) in
  assert_equal is should_be

let test_get_width c =
  assert_equal (get_width 0) 0;
  assert_equal (get_width 1) 1;
  assert_equal (get_width 2) 1;
  assert_equal (get_width 12) 2;
  assert_equal (get_width 123) 3;
  assert_equal (get_width 1234) 4

let test_dec_to_ratio c =
  assert_equal (ratio_of_decimal (Decimal(0,0,0))) (Ratio (0,1));
  assert_equal (ratio_of_decimal (Decimal(0,1,0))) (Ratio(1, 10));
  assert_equal (ratio_of_decimal (Decimal(0,2,0))) (Ratio (2, 10));
  assert_equal (ratio_of_decimal (Decimal(0,22,0))) (Ratio (22, 100));
  assert_equal (ratio_of_decimal (Decimal(0,2,1))) (Ratio (2, 100));
  assert_equal (ratio_of_decimal (Decimal(0,1,1))) (Ratio(1,100));
  assert_equal (ratio_of_decimal (Decimal (1,22,0))) 
               (reduce_ratio (Ratio(122, 100)))

let test_int_pow c =
  assert_equal (int_pow 8 0) 1;
  assert_equal (int_pow 45 1) 45;
  assert_equal (int_pow 2 2) 4;
  assert_equal (int_pow 3 3) 27
  

let test_add c =
  let weights = [Ratio(1,2); Ratio(1,3); Ratio(2,3)] in
  let n = List.fold_left add (ratio_of_int 0) weights in
  assert_equal n (ReducedRatio(3, 2))

let test_normalize c =
  let weights = [Ratio(4,1); Ratio(6,1)] in
  let n = List.fold_left add (ratio_of_int 0) weights in
  assert_equal n (ReducedRatio (10, 1));
  assert_equal (List.map (fun w -> divide w n) weights) [ReducedRatio(2, 5); ReducedRatio(3, 5)]

let test_normalize_idem c =
  let weights = [Ratio(9,10); Ratio(1,10)] in
  let n = List.fold_left add (ratio_of_int 0) weights in
  assert_equal n (ReducedRatio(1,1));
  assert_equal (List.map (fun w -> divide w n) weights) [ReducedRatio(9,10); ReducedRatio(1,10)]
  
(* Name the test cases and group them together *)

let suite =
  "suite">:::
    [
      "test_prime_prime">:: test_prime_prime;
      "test_prime_not_prime">:: test_prime_not_prime;
      "test_next_prime_base">:: test_next_prime_base;
      "test_next_prime_ind">:: test_next_prime_ind;
      "test_is_prime_10">:: test_is_prime_10;
      "test_is_prime_11">:: test_is_prime_11;
      "test_reduce_ratio">:: test_reduce_ratio;
      "test_reduce_R">::  test_reduce_R;
      "test_reduce_I">:: test_reduce_I;
      "test_reduce_D">:: test_reduce_D;
      "test_reduce_S">:: test_reduce_S;
      "test_int_pow">:: test_int_pow;
      "test_get_width">:: test_get_width;
      "test_dec_to_ratio">:: test_dec_to_ratio;
      "test_ratio_decimal">:: test_ratio_decimal;
      "test_add">:: test_add;
      "test_normalize">:: test_normalize;
      "test_normalize_idem">::test_normalize_idem
     ]

let () = 
  Printf.printf "Running %s" __FILE__;
  run_test_tt_main suite
