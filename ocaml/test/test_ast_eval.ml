open OUnit2
open Programs_aux

open Mock_targets.PlanOut
open Po_syntax

let test_sort ctxt = 
  let open Config in 
  (* length(a) + (10 * 2 + (2 * (20 % b)) / 5) *)
  let a = GetContainer (ExtSource, External, "a", 0, Unknown) in 
  let b = GetNumber (ExtSource, External, "b", 0) in 
  let aexpr = Abinop (Sum, 
    Length a, Abinop (Sum, 
      Abinop (Product, 
        PONumber (Oratio.ratio_of_int 10),
        PONumber (Oratio.ratio_of_int 2)),
      Abinop (Div,
        Abinop (Product,
          PONumber (Oratio.ratio_of_int 2),
          Abinop (Mod, 
            PONumber (Oratio.ratio_of_int 20),
            b)),
        PONumber (Oratio.ratio_of_int 5)))) in 
  let is        = Ast.Eval.sort aexpr in 
  let should_be = Abinop (Sum,
    PONumber (Oratio.ratio_of_int 20),
    Abinop (Sum,
      Length a, 
      Abinop (Product,
        PONumber (Oratio.ReducedRatio (2, 5)),
          Abinop (Mod, 
            PONumber (Oratio.ratio_of_int 20), 
            b)))) in 
  (*print_ast (Program (Expr (Aexpr is))); 
  print_ast (Program (Expr (Aexpr should_be)));*)
  assert_equal is should_be 

let suite = 
  "suite">:::[
    "test_sort">::test_sort;
  ]

let () = 
  Printf.printf "Running %s" __FILE__;
  run_test_tt_main suite