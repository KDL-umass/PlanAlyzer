open Assumptions

module Logger = Logging.Make(struct 
    let file = __FILE__
    let phase = Logging.Estimators
  end)

module MakeAte (Cpo: sig 
  include Corepo
  module Ddg : Ddg.Ddg 
  with type key = Config.ssa_id 
end 
with type Sigma.key = string
) = struct 

  module A = MakeAssumptions(Cpo)

  let static_assumptions = [  
      A.between_subjects ~unit_analysis:None ~const_only:true; 
      (* A.no_time_variance *)
    ]
  
  let dynamic_assumptions = []

  let check_static_assumptions (p: Cpo.program) : bool = 
    List.for_all (fun f -> (f p)#check_assumption) static_assumptions

  (* TODO: ppx macro that maps the fields of the treatments and the conditioning
     sets to a record corresponding to column names in a database. *)

  module PairwiseFormat = struct 
      open Printf

      let string_of_treatments dt = 
        Utils.join ", " (fun (k, v) -> sprintf "%s=%s" k
            (Cpo.Format.string_of_inlang_expr v))
          (Cpo.Delta.bindings dt)
      
      let string_of_contrast (dt1, dt2) = 
        let (d1, r1, phi1) = dt1 in 
        let (d2, r2, phi2) = dt2 in 
        let phi = Cpo.Phi.union phi1 phi2 in 
        sprintf 
          "Avg(Y|%s) - Avg(Y|%s) (%s vs. %s)%s"
          (* "&#163;%s&#164;%s&#163;%s" *)
          (string_of_treatments d1)
          (string_of_treatments d2)
          (Oratio.string_of_ratio r1)
          (Oratio.string_of_ratio r2)
          (if Cpo.Phi.cardinal phi <> 0
           then "&#165;" ^ Cpo.Format.string_of_phi phi
           else "")

      let string_of_semantic_tuple (tupe : Cpo.semantic_tuple) = 
        let (dt_pairs, cond_set) = tupe in 
        let pairs = Utils.all_pairs dt_pairs
          (* Remove comparisons between treatments with non-equal keys. *)
          |> List.filter (fun ((p1,_,_), (p2,_,_)) ->
              let keys1 = Cpo.Delta.bindings p1 |> List.map fst in 
              let keys2 = Cpo.Delta.bindings p2 |> List.map fst in 
              List.for_all (fun k -> List.mem k keys2) keys1 &&
              List.for_all (fun k -> List.mem k keys1) keys2
              )
          (* Remove self-comparisons *)
          |> List.filter (fun ((p1, _,_), (p2,_,_)) ->
              not (Cpo.Delta.equal (fun a b -> compare a b = 0) p1 p2)) 
          (* Remove duplicates *)
          |> Utils.uniq in 
        sprintf "Conditioning set: \n%s\n============\n%s\n" 
          (Cpo.Format.string_of_cond_set cond_set)
          (Utils.join "\n" string_of_contrast pairs)
          

      let string_of_pairwise_comparisons (tupes : Cpo.semantic_tuple list) = 
        (* Traverse the DDG, starting with the roots. For each node, if an 
        ancestor appears in the conditioning set of its phi set, then it cannot 
        be included in comparisons. *)
        Utils.join "\n" string_of_semantic_tuple tupes

    end

  module QueryableTables = struct 
    open Printf
    type condition = (string * Cpo.inlang_expr) list 
    type cond_set_table_entry = {
      exp_id      : int;
      cond_set_id : int;
      param_name  : string [@default "NULL"];
      param_value : string [@default "NULL"];
      thunk       : string [@default "NULL"];
      synthetic   : bool   [@default false];
    } [@@deriving make]
    type treatment_set_table_entry = {
      exp_id          : int;
      cond_set_id     : int;
      treatment_id    : int;
      prob            : float;
      treatment_name  : string [@default "NULL"];
      treatment_value : string [@default "NULL"];
      thunk           : string [@default "NULL"];
      synthetic       : bool   [@default false];
    } [@@deriving make]

    let cond_set_counter = ref 0
    let treatment_counter = ref 0    

    let get_origin k = 
      let m : Config.origin Cpo.OriginMap.t = !Cpo.origin_map in 
      if Cpo.OriginMap.mem (k, 0) m 
      then Cpo.OriginMap.find (k, 0) m
      else Cpo.OriginMap.find (k, 1) m
  
    let make_cond_set_table exp_id cond_set_id cset = 
      let (eagers, thunks) = cset in 
      let tab : cond_set_table_entry list = eagers
        |> Cpo.Sigma.bindings
        |> List.map (fun ((k : string), (v : Cpo.inlang_expr)) ->
            make_cond_set_table_entry
              ~exp_id
              ~cond_set_id
              ~param_name:k
              ~param_value:(Cpo.Format.string_of_inlang_expr v)
              ~synthetic:(get_origin k = Config.Synth)
              ()
            ) in 
      thunks
      |> Cpo.Phi.elements
      |> List.map (fun (e : Cpo.inlang_expr) -> 
          make_cond_set_table_entry
            ~exp_id
            ~cond_set_id
            ~thunk:(Cpo.Format.string_of_inlang_expr e)
            ()
        )
      |> (@) tab 
      
    let make_treatment_table exp_id cond_set_id tmt = 
      let eager, p, thunks = tmt in 
      let prob = Oratio.float_of_ratio p in 
      let treatment_id = (incr treatment_counter; !treatment_counter) in 
      let tab : treatment_set_table_entry list = eager
        |> Cpo.Delta.bindings
        |> List.map (fun (k, v) ->
          make_treatment_set_table_entry
              ~exp_id
              ~cond_set_id
              ~treatment_id
              ~prob
              ~treatment_name:k
              ~treatment_value:(Cpo.Format.string_of_inlang_expr v)
              ~synthetic:(get_origin k = Config.Synth)
              ()
              ) in 
      thunks
      |> Cpo.Phi.elements
      |> List.map (fun (e : Cpo.inlang_expr) -> 
          make_treatment_set_table_entry
            ~exp_id
            ~cond_set_id
            ~treatment_id
            ~prob
            ~thunk:(Cpo.Format.string_of_inlang_expr e)
            ()
        )
      |> (@) tab 

    let make_table_data exp_id (data: Cpo.semantic_tuple) =
      let treatments, cond_set = data in 
      let cond_set_id = (incr cond_set_counter; !cond_set_counter) in 
      make_cond_set_table exp_id cond_set_id cond_set, 
      List.map (make_treatment_table exp_id cond_set_id) treatments 


    let make_tables exp_id (data: Cpo.semantic_tuple list) = 
      let cond_set_tables, treatment_tables = 
        List.map (make_table_data exp_id) data 
        |> List.split in 
      List.flatten cond_set_tables, 
      List.flatten treatment_tables |> List.flatten

    let cond_set_table_headers = 
      "exp_id,cond_set_id,param_name,param_value,thunk,synthetic"

    let treatment_table_headers =
      "exp_id,cond_set_id,treatment_id,prob,treatment_name,treatment_value,thunk,synthetic"

    let cond_set_table_to_csv_data (datum : cond_set_table_entry) = 
      sprintf "%d,%d,%s,\"%s\",\"%s\",%b" 
        datum.exp_id
        datum.cond_set_id
        datum.param_name
        (Str.global_replace (Str.regexp_string "\"") "\"\"" 
          datum.param_value)
        (Str.global_replace (Str.regexp_string "\"") "\"\"" datum.thunk )
        datum.synthetic

    let treatment_to_csv_data (datum : treatment_set_table_entry) = 
      sprintf "%d,%d,%d,%f,%s,\"%s\",\"%s\",%b"
        datum.exp_id
        datum.cond_set_id
        datum.treatment_id
        datum.prob
        datum.treatment_name
        (Str.global_replace (Str.regexp_string "\"") "\"\"" 
          datum.treatment_value)
        (Str.global_replace (Str.regexp_string "\"") "\"\"" 
          datum.thunk)
        datum.synthetic

    let ate_to_csv_data folder exp_id (data: Cpo.semantic_tuple list) = 
      let cond_set_tables, treatment_tables = make_tables exp_id data in 
      let conds = open_out (folder ^ "/conds.csv") in 
      fprintf conds "%s\n" cond_set_table_headers;
      List.iter (fun record -> 
      (* for i=0 to List.length cond_set_tables - 1 do  *)
        (* let table = List.nth cond_set_tables i in  *)
        fprintf conds "%s\n" (cond_set_table_to_csv_data record)
      (* done; *)
      ) cond_set_tables;
      close_out conds;
      let treats = open_out (folder ^ "/treatments.csv") in 
      fprintf treats "%s\n" treatment_table_headers;
      List.iter (fun record -> 
        fprintf treats "%s\n" (treatment_to_csv_data record))
        treatment_tables;
      close_out treats

      (* let cond_set_string = 
        Utils.join "\n" cond_set_table_to_csv_data cond_set_tables in 
      let treatment_string = 
        Utils.join "\n" treatment_to_csv_data treatment_tables in 
      cond_set_table_headers ^ "\n" ^ cond_set_string, 
      treatment_table_headers ^ "\n" ^ treatment_string *)

    (* let query outcome_col_name (cond1 : condition) (cond2 : condition) = 
      sprintf 
        "SELECT AVG(T1.%s) - AVG(T2.%s) 
         FROM %s as T1, %s as T2, %s as C
         WHERE " 
         outcome_col_name outcome_col_name
         metric_table metric_table *)


  end 

  let get_all_versions g s = 
    Cpo.Ddg.nodes g
    |> List.filter (fun (s', _) -> s = s')

  let get_all_treatments tlist = tlist
    |> List.map (fun (d, p, _) -> Cpo.Delta.bindings d)
    |> List.flatten
    |> List.map fst 
    |> Utils.uniq

  let get_all_ancestors g all_treatments = all_treatments 
    |> List.map (fun s -> get_all_versions g s
        |> List.map (Cpo.Ddg.get_ancestors g) 
        |> List.flatten)
    |> List.flatten
    |> Utils.uniq 
    |> List.map fst 

  let filter_out_dynamic g program tupes : Cpo.semantic_tuple list = 
    (* Grab all of the time varying vars. *)
    let time_varying : string list = List.fold_left (fun tvvars pi -> 
      tvvars @ (Utils.filter_map (fun n -> match n with 
        | Cpo.Declare (_, {Cpo.dyn}, _)
        | Cpo.Assign (_, _, {Cpo.dyn}, _) when dyn = Config.Tv -> 
          Cpo.delta_key_from_node n
        | _ -> None)
        pi)) [] program
      |> Utils.uniq in 
    (* Filter the time-varying variables from the treatments and conditioning 
       sets *)
    tupes
    |> Utils.filter_map (fun (_, (cset, _) as tupe) ->
        if Cpo.Sigma.exists (fun k _ -> List.mem k time_varying) cset 
        then None
        else Some tupe)
    |> List.map (fun ((tlist : Cpo.treatment list), (cset, p) as tupe) ->
      let tlist = tlist
        |> Utils.filter_map (fun (d, t, p) ->
          (* If a time-varying variable appears in the treatment, remove it. *)
          let d' = Cpo.Delta.filter 
            (fun k _ -> not (List.mem k time_varying)) d in 
          if Cpo.Delta.is_empty d'
          then None
          else Some (d', t, p)) in 
      (* Remove from conditioning set any variables that *only* flow into time-
         varying variables. *)
      let all_treatments = get_all_treatments tlist in 
      let all_ancestors = get_all_ancestors g all_treatments in 
      let cset = Cpo.Sigma.fold (fun k _ ->  
          if List.mem k all_ancestors 
          then Utils.identity 
          else Cpo.Sigma.remove k)
        cset cset in 
      (tlist, (cset, p))
    )

  let filter_cant_evaluate g program tupes = tupes
    (* Remove phis and any downstream conditions or treatments. *)
    |> Utils.filter_map (fun (dtlist, (s, phis)) -> 
      (* Get variables in phis *)
      let phi_vars  : Cpo.Sigma.key list = Cpo.get_phi_varnames phis in 
      let dtlist' = List.map (fun (d, p, r) -> 
          (* For each treatment in d, if the treatment has an ancestor in 
             phi_vars, remove d. *)
          let d' = List.fold_left (fun d (k, _) -> 
              let treatment_ancestors = get_all_ancestors g [k] in 
              let not_in_phis : bool = treatment_ancestors 
                |> List.for_all (fun a -> not (List.mem a phi_vars)) in 
              if not_in_phis
              then d 
              else Cpo.Delta.remove k d) 
            d (Cpo.Delta.bindings d) in 
          (d, Oratio.neg_one, Cpo.Phi.empty)
        ) dtlist in 
      if List.length dtlist' > 0 
      then Some (dtlist', (s, Cpo.Phi.empty))
      else None 
    )

  let filter_unrelated_conditions g program tupes = tupes
    |> List.map (fun ((dtlist : Cpo.treatment list), (s, phis)) ->
        (* Get all the treatment keys. *)
        let dt_keys = dtlist 
          |> List.map Utils.fst3 
          |> List.map Cpo.Delta.bindings 
          |> List.flatten
          |> List.map fst 
          |> Utils.uniq  
          in 
        let treatment_ancestors = 
          get_all_ancestors g dt_keys in 
        Logger.print_debug __LINE__
          (format_of_string "\n\tdt_keys: [%s]\n\tancestors: [%s]")
          (Utils.join "; " Utils.identity dt_keys)
          (Utils.join "; " Utils.identity treatment_ancestors);
        let s' = List.fold_left (fun s (k, _) -> 
            if List.mem k dt_keys || List.mem k treatment_ancestors
            then s 
            else Cpo.Sigma.remove k s 
          ) s (Cpo.Sigma.bindings s) in 
        (dtlist, (s', phis))
      )

  let merge_singleton_treatments g program (tupes : Cpo.semantic_tuple list) = 
    (* Select out the singleton treatments. *)
    let (singletons, others) = List.partition (fun (dtlist, _) -> 
        List.length dtlist = 1) tupes in 
    Printf.sprintf "number of singletons: %d" (List.length singletons);
    (* Find the intersection of treatments *)
    let module Treatment = Set.Make(String) in 
    let treatments = singletons (* semantic_tuple list *)
      |> List.map fst (* treatment list list *)
      (* We know there is only one treatment, therefore one delta per item *)
      |> List.flatten 
      |> List.map Utils.fst3 (* delta list *)
      |> List.map Cpo.Delta.bindings (* key list list *)
      |> List.map (List.map fst) (* string list list *)
      |> List.map Treatment.of_list in 
    let min_common_treatment = List.fold_left 
      Treatment.inter 
      (List.fold_left Treatment.union Treatment.empty treatments) 
      treatments in 
    (* If this is empty, return; o/w remove treatments from each set. *)
    if Treatment.cardinal min_common_treatment = 0 
    then tupes
    else begin 
      let singletons' = List.map (fun (dtlist, (s, p)) -> 
        let dtlist' = List.map (fun (d, r, p) -> 
            let d' = List.fold_left (fun d' k -> 
                (* Build up a new treatment environment that only contains the 
                   min common treatments. *)
                let v = Cpo.Delta.find k d in 
                Cpo.Delta.add k v d') 
              Cpo.Delta.empty
              (Treatment.elements min_common_treatment) in 
              (d', r, p)) 
          dtlist in
        (dtlist', (s, p))) singletons in
      (* Run filter_unrelated_conditions to remove unncessary deps. *)
      others @ (filter_unrelated_conditions g program singletons')
    end 

  (* let promote_phi_assertions g program tupes = tupes 
    |> List.map (fun (dt_list, (s, phi)) -> 
        let assertions = Cpo.get_assertions phi in 
        let assignments = get_truth_assignments assertions in 
        let dt_list' = List.map (fun (d, ))
      ) *)
  
  let string_of_pairwise_contrasts g program tupes = 
    Logger.print_debug __LINE__ "%s\n" (Cpo.Ddg.string_of_graph g);
    ignore (check_static_assumptions program);
    let apply_op tupes fn = 
      fn g program tupes 
      |> Cpo.merge_equivalent_conditioning_sets in
    let ops = [
      filter_unrelated_conditions; 
      filter_out_dynamic;
      filter_cant_evaluate;
      merge_singleton_treatments
      ] in 
    List.fold_left apply_op tupes ops 
    |> PairwiseFormat.string_of_pairwise_comparisons 
end 

module MakeCgm (Cpo : sig 
  include Corepo.Corepo 
  val get_delta_key : Config.ssa_id -> string 
  val get_references : inlang_expr -> Config.ssa_id list 
  val is_constant : inlang_expr -> bool 
  end ) = Cgm.Make(struct
    module M = struct
      type key = string 
      type program = Cpo.program
      type path = Cpo.pi 
      let key_compare k1 k2 = compare k1 k2 
      let key_to_str k = k
      let sexp_of_key k = Sexplib.Conv.sexp_of_string k
      let key_of_sexp s = Sexplib.Conv.string_of_sexp s
      let get_path_variables (path : path) : key list = 
        List.fold_left (fun lst n -> match n with 
          | Cpo.Declare ((s, _), _, _) -> 
            assert (not (List.mem s lst)); s::lst
          | Cpo.Assign (o, (s, _), _, e) ->
            if List.mem s lst || Cpo.is_constant e 
            then lst 
            else s::lst
          | _ -> lst
         ) [] path
      let find_dependents (p : path) k : key list = 
        let rec helper found = function 
          | [] -> []
          | h::t -> 
            if found 
            then begin match h with 
                | Cpo.Assign (_, s, _, e) ->
                  let refs = Cpo.get_references e 
                             |> List.map Cpo.get_delta_key in 
                  if List.mem k refs 
                  then (Cpo.get_delta_key s)::(helper found t)
                  else helper found t
                | _ -> helper found t
              end 
            else begin match h with  
                | Cpo.Assign (_, s, _, _)
                | Cpo.Declare (s, _, _) when (Cpo.get_delta_key s) = k -> 
                  helper true t
                | _ -> helper found t
              end in 
          helper false p 
      let get_program_variables program = 
        List.map get_path_variables program 
        |> List.flatten
        |> Utils.uniq
      end

    include M 
    module G = Graph.Make(M)
    open G
    let output_var = "^Y"
  end)
