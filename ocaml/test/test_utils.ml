open OUnit2
open Utils

let test_range_negative ctxt = ()
  

let test_enumerate ctxt = ()

let suite = 
  "suite">:::[
    "test_range">::test_range_negative;
    "test_enumerate">::test_enumerate
  ]

let () = 
  run_test_tt_main suite