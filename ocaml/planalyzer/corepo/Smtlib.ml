include Smtlib_syntax
open Sexplib.Conv

module Logger = Logging.Make(struct 
    let file = __FILE__
    let phase = Logging.Corepo 
  end)

(* Stuff above SMT lib. *)
type identifier =
  | Id of string
[@@deriving sexp] 

let string_of_identifier = function
  | Id s -> "Id " ^ s

type term =
  | String of string
  | Int of int
  | BitVec of int * int
  | Const of identifier
  | App of identifier * term list
  | Let of string * term * term

let rec string_of_term t =
  let open Printf in
  match t with
  | String s -> sprintf "String %s" s
  | Int i -> sprintf "Int %d" i
  | BitVec (i1, i2) -> sprintf "BitVec (%d, %d)" i1 i2
  | Const id -> sprintf "Const %s" (string_of_identifier id)
  | App (id, tlist) -> sprintf "App (%s, [%s])"
			       (string_of_identifier id)
			       (Utils.join "; " string_of_term tlist)
  | Let (s, t1, t2) -> sprintf "Let (%s, %s, %s)" s
			       (string_of_term t1)
			       (string_of_term t2)

type sort =
  | Sort of identifier
  | SortApp of identifier * sort list
  | BitVecSort of int
[@@deriving sexp] 
  
let int_sort  = Sort (Id "Int")
let bool_sort = Sort (Id "Bool")  
let string_sort = Sort (Id "String")  
let array_sort dom rng = SortApp (Id "Array", [dom; rng])

let string_of_sort s = 
  if s = int_sort then "Int"
  else if s = bool_sort then "Bool"
  else if s = string_sort then "String"
  else sexp_of_sort s |> Sexplib.Sexp.to_string

let rec ast_string_of_sort t = match t with 
  | Sort (Id s) -> Printf.sprintf "Sort (Id \"%s\")" s
  | SortApp (Id s, slist) -> 
    Printf.sprintf "Sort (Id \"%s\", [%s])" s
      (Utils.join "; " ast_string_of_sort slist)
  | BitVecSort _ -> assert false 

exception UnparsableTerm of sexp 
exception SMTError of string 

let int_to_term n = Int n
  
let const x = Const (Id x)

let true_const = Const (Id "true")
let false_const = Const (Id "false")

let bool_to_term b = match b with
  | true -> true_const
  | false -> false_const


let string_to_term s = String s

let ite e1 e2 e3 = App (Id "ite", [e1; e2; e3])
let app2 x term1 term2 = App (Id x, [term1; term2])
let app1 x term = App (Id x, [term])
let app0 x = App (Id x, [])
let equals = app2 "="
let implies = app2 "=>"
let add = app2 "+"
let sub = app2 "-"
let mul = app2 "*"
let lt = app2 "<"
let gt = app2 ">"
let lte = app2 "<="
let gte = app2 ">="
 
let and_ term1 term2 = match (term1, term2) with
  | (App (Id "and", alist1), App (Id "and", alist2)) -> 
    App (Id "and", alist1 @   alist2)
  | (App (Id "and", alist1), _) -> App (Id "and", alist1 @ [ term2 ])
  | (_, App (Id "and", alist2)) -> App (Id "and", term1 :: alist2)
  | _ -> App (Id "and", [term1; term2])

let or_ term1 term2 = match (term1, term2) with
  | (App (Id "or", alist1), App (Id "or", alist2)) -> 
    App (Id "or", alist1 @   alist2)
  | (App (Id "or", alist1), _) -> App (Id "or", alist1 @ [ term2 ])
  | (_, App (Id "or", alist2)) -> App (Id "or", term1 :: alist2)
  | _ -> App (Id "or", [term1; term2])

let not_ term = App (Id "not", [term])

let rec term_to_string term =
  let open Printf in
  match term with 
  | String s -> "String " ^ s
  | Int n -> "Int " ^ (string_of_int n)
  | BitVec (n, w) -> failwith "my language has no bit vectors"
  | Const x -> "Const " ^ (string_of_identifier x)
  | App (f, args) -> Printf.sprintf "App (%s, [%s])"
				    (string_of_identifier f)
				    (Utils.join "; " term_to_string args)
  | Let (x, term1, term2) -> Printf.sprintf "Let (%s, %s, %s)"
					    x
					    (term_to_string term1)
					    (term_to_string term2)

(* module type Smtlib = sig 
  type solver 
  val make_solver : string -> solver 
  val solver_mock : unit -> solver
  val check_mock : bool -> bool
  end  *)

module Make(CPO : sig 
    type cpo_expr 
    type basetype 
    val mock : bool
    val exp_to_term : cpo_expr -> term 
    val id_of_base_type : ?aux_args:(basetype list) -> basetype -> sort option
  end) = struct 
  (* The sexp that needs to be converted to a string and sent to z3 *)
  open Printf             
  (* Internal S-expression representation. *)
  exception SmtTermError of CPO.cpo_expr
  
  let _mock = ref CPO.mock 
  let check_mock switch = (if switch then _mock := not !_mock); !_mock
	       
  type real_solver = { 
    stdin : out_channel; 
    stdout : in_channel; 
    stdout_lexbuf : Lexing.lexbuf 
    } 

  type solver = MockSolver | RealSolver of real_solver

  (* Does not flush *)
  let rec write_sexp (out_chan : out_channel) (e : sexp): unit = match e with
    | SInt n -> output_string out_chan (string_of_int n)
    | SBitVec (n, w) -> Printf.fprintf out_chan "(_ bv%d %d)" n w
    | SSymbol str -> output_string out_chan str
    | SKeyword str -> output_string out_chan str
    | SString str -> output_string out_chan ("\"" ^ str ^ "\"")
    | SList lst ->
      (output_char out_chan '(';
       write_sexp_list out_chan lst;
       output_char out_chan ')')
  
  and write_sexp_list (out_chan : out_channel) (es : sexp list) : unit =
    match es with
      | [] -> ()
      | [e] -> write_sexp out_chan e
      | e :: es ->
        (write_sexp out_chan e;
         output_char out_chan ' ';
         write_sexp_list out_chan es)
  
  let write (solver : solver) (e : sexp) : unit = match solver with 
    | MockSolver -> ()
    | RealSolver solver ->
      write_sexp solver.stdin e;
      output_char solver.stdin '\n';
      flush solver.stdin
  
  let read (solver : solver) : sexp = match solver with 
    | MockSolver -> SSymbol "mock-success"
    | RealSolver solver ->
      Smtlib_parser.sexp Smtlib_lexer.token solver.stdout_lexbuf
  
  (* Sends a single command to z3 and awaits the response? *)
  let command (solver : solver) (sexp : sexp) = 
    write solver sexp; read solver
  
  let print_success_command =
    SList [SSymbol "set-option"; SKeyword ":print-success"; SSymbol "true"]

  let produce_models = 
    SList [SSymbol "set-option"; SKeyword ":produce-models"; SSymbol "true"]
  
  (* keep track of all solvers we spawn, so we can close our read/write
     FDs when the solvers exit *)
  let _solvers : (int * solver) list ref = ref []
  
  let handle_sigchild (_ : int) : unit =
    if check_mock false then () else 
    let open Printf in
    try
      let (pid, status) = Unix.waitpid [] (-1) in
      Log.info "solver child (pid %d) exited\n%!" pid;
      let solver = List.assoc pid !_solvers in
      match solver with 
      | RealSolver solver ->
        close_in_noerr solver.stdout; close_out_noerr solver.stdin
      | MockSolver -> ()
    with
      _ -> ()
  
  let () = 
    if check_mock false then () else 
    Sys.set_signal Sys.sigchld (Sys.Signal_handle handle_sigchild)
  
  let make_solver (z3_path : string) : solver =
    if check_mock false then MockSolver else
    try
    let open Unix in
    let (z3_stdin, z3_stdin_writer) = pipe () in
    let (z3_stdout_reader, z3_stdout) = pipe () in
    (* If the ocaml ends of the pipes aren't marked close-on-exec, they
       will remain open in the fork/exec'd z3 process, and z3 won't exit
       when our main ocaml process ends. *)
    let _ = set_close_on_exec z3_stdin_writer; 
            set_close_on_exec z3_stdout_reader; in
    let pid = create_process z3_path [| z3_path; "-in"; "-smt2" |]
      z3_stdin z3_stdout stderr in
    let in_chan = in_channel_of_descr z3_stdout_reader in
    let out_chan = out_channel_of_descr z3_stdin_writer in
    set_binary_mode_out out_chan false;
    set_binary_mode_in in_chan false;
    let solver = RealSolver { 
      stdin = out_chan; 
      stdout = in_chan; 
      stdout_lexbuf = Lexing.from_channel in_chan 
      } in
    _solvers := (pid, solver) :: !_solvers;
    begin try
      match command solver print_success_command with
        | SSymbol "success" -> 
          begin match command solver produce_models with 
            | SSymbol "success" -> solver
            | _ -> failwith "could not configure solver to :produce-models"
          end
        | _ -> failwith "could not configure solver to :print-success"
    with
      | Sys_error msg when msg = "Bad file descriptor" -> 
        failwith "couldn't talk to solver,   double-check path" end
    with Unix.Unix_error (code, s1, s2) -> failwith ("asdf" ^ s1)

  
  (* What actually gets sent to z3 *)
  let sexp_to_string (sexp : sexp) : string =
    let open Buffer in
    let buf = create 100 in
    let rec to_string (sexp : sexp) : unit = match sexp with
      | SList alist -> add_char buf '('; list_to_string alist; add_char buf ')'
      | SSymbol x -> add_string buf x;
      | SKeyword x -> add_string buf x;
      | SString x -> add_char buf '"'; add_string buf x; add_char buf '"'
      | SInt n -> add_string buf (string_of_int n)
      | SBitVec (n, w) -> add_string buf (Format.sprintf "(_ bv%d %d)" n w)
    and list_to_string (alist : sexp list) : unit = match alist with
      | [] -> ()
      | [x] -> to_string x
      | x :: xs -> to_string x; add_char buf ' '; list_to_string xs in
    to_string sexp;
    contents buf
  
  type check_sat_result =
    | Sat
    | Unsat
    | Unknown
    [@@deriving show]
  
  let rec string_of_sort s =
    let open Printf in
    match s with 
    | Sort id -> sprintf "Sort %s" (string_of_identifier id)
    | SortApp (id, slist) -> sprintf "SortApp (%s, [%s])"
  				   (string_of_identifier id)
  				   (Utils.join "; " string_of_sort slist)
    | BitVecSort i -> sprintf "BitVecSort %d" i
  

  
  let id_to_sexp (id : identifier) : sexp = match id with
    | Id x -> SSymbol x
  
  let rec sort_to_sexp (sort : sort) : sexp = match sort with
    | Sort x -> id_to_sexp x
    | SortApp (x, sorts) ->
      SList ((id_to_sexp x) :: (List.map sort_to_sexp sorts))
    | BitVecSort n -> SList [ SSymbol "_"; SSymbol "BitVec"; SInt n ]
  
  let rec term_to_sexp (term : term) : sexp = match term with
    | String s -> SString s
    | Int n -> SInt n
    | BitVec (n, w) -> SBitVec (n, w)
    | Const x -> id_to_sexp x
    | App (f, args) -> SList (id_to_sexp f :: (List.map term_to_sexp args))
    | Let (x, term1, term2) ->
      SList [SSymbol "let";
             SList [SList [SSymbol x; term_to_sexp term1]];
             term_to_sexp term2]
  

  
  let rec sexpr_to_string sexp : string = match sexp with
    | SString s -> sprintf "(SString %s)" s
    | SList l -> sprintf "(SList [%s])" (Utils.join "; " sexpr_to_string l)
    | SSymbol s -> sprintf "(SSymbol %s)" s
    | SKeyword s -> sprintf "(SKeyword %s)" s
    | SInt i -> sprintf "(SInt %d)" i
    | SBitVec (i, j) -> sprintf "(SBitVec (%d, %d))" i j 
  
  let rec sexp_to_term (sexp : sexp) : term = match sexp with
    | SString s -> String s
    | SInt n -> Int n
    | SList [(SSymbol (-)); (SInt n)] -> Int (-n)
    | SBitVec (n, w) -> BitVec (n, w)
    | SSymbol x -> Const (Id x)
    | e ->
       printf "unparsable term: %s\n"  (sexpr_to_string e);
       raise (UnparsableTerm e)
  
  let expect_success (solver : solver) (sexp : sexp) : unit =
    match command solver sexp with
    | SSymbol "success" -> ()
    | SSymbol "mock-success" ->
      (match solver with MockSolver -> () | _ -> assert false)
    | SList [SSymbol "error"; SString x] -> failwith x
    | sexp -> failwith ("expected either success or error from solver, got " ^
                        (sexp_to_string sexp))
  
  let declare_const (solver : solver) (id : identifier) (sort : sort option) 
  : bool =
    match sort with 
    | None -> 
      Log.debug "Not declaring %s\n" (string_of_identifier id);
      false
    | Some sort ->
      (*Printf.printf "Declaring %s\n" (string_of_identifier id);*)
      expect_success solver (SList 
        [SSymbol "declare-const"; id_to_sexp id; sort_to_sexp sort]);
      true 
  
  let declare_fn (solver : solver) (id: identifier) (argsorts : sort list)   
  (return_type : sort) : unit =
    expect_success solver (SList [SSymbol "declare-fun";
  				id_to_sexp id;
  				(SList (List.map sort_to_sexp argsorts));
  				sort_to_sexp return_type])
  
  
  let assert_ (solver : solver) (term : term) : unit =
    expect_success solver (SList [SSymbol "assert"; term_to_sexp term])
  
  let check_sat (solver : solver) : check_sat_result =
    match command solver (SList [SSymbol "check-sat"]) with
    | SSymbol "sat" -> Sat
    | SSymbol "unsat" -> Unsat
    | SSymbol "unknown" -> Unknown
    | sexp -> failwith ("unexpected result from (check-sat), got " ^
                        sexp_to_string sexp)
  
  let get_model (solver : solver) : (identifier * term) list =
    let rec read_model sexp = match sexp with
      | [] -> []
      | (SList [SSymbol "define-fun"; SSymbol x; SList []; _; sexp]) :: rest ->
        (Id x, sexp_to_term sexp) :: read_model rest
      | _ :: rest -> read_model rest in
    match command solver (SList [SSymbol "get-model"]) with
    | SList (SSymbol "model" :: alist) -> read_model alist
    | sexp -> failwith ("expected model, got " ^ (sexp_to_string sexp))

  let get_values (solver: solver) (ids : identifier list) : (identifier * term) list = 
    let ids = List.map (fun (Id id) -> SSymbol id) ids in 
    let rec read_value sexp = match sexp with
      | [] -> []
      | (SList [SSymbol x; v])::rest ->
        (Id x, sexp_to_term v) :: read_value rest 
      | _ :: rest -> read_value rest in 
    match command solver (SList [SSymbol "get-value"; SList ids]) with 
      | SList lst -> read_value lst
      | sexp -> failwith ("expected value, got " ^ (sexp_to_string sexp))
  
  let push (solver : solver) = expect_success solver (SList [SSymbol "push"])
  let pop (solver : solver) = expect_success solver (SList [SSymbol "pop"])
  
  		       
  let bv_sort w = BitVecSort w
  
  
  end