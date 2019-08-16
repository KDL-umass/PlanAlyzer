include Corepo 

module MakeAssumptions (Cpo: Corepo) : sig 
    val between_subjects : ?unit_analysis : string option -> 
                           ?const_only : bool -> Cpo.program -> 
      < check_assumption : bool >  
    val no_time_variance : Cpo.program -> < check_assumption : bool >
   end = struct

  exception Assumption_error of string * string * string 

  let make_assumption_error ~name ~msg ~witness = 
    Assumption_error (name, msg, witness)

  let make_witness h path = 
    Printf.sprintf "Statement\n\t%s\nin path\n\t%s" 
      (Cpo.Format.string_of_node h)  
      (Cpo.Format.string_of_path path)

  let between_subjects ?(unit_analysis=None) 
                       ?(const_only=false) prog = object 

      val err = make_assumption_error ~name:"between_subjects"
      
      method check_assumption = 
        let check_assumption_path path = 
          let unita = ref unit_analysis in 
          let open Config in 
          let open Cpo in 
          let msg2 = "Multiple units of randomization." in 
          let msg1 = 
            "Unit of randomization not equal to unit of analysis." in 
          let rec helper path = match path with 
            | [] -> true 
            | Declare (_, {rand=(Config.Rand [])}, _)::_  
            | Assign (_, _, {rand=(Config.Rand [])}, _)::_ -> assert false 
            | (Assign (_, _, {dyn; rand=(Config.Rand [unitr])}, _) as h)::t
            | (Declare (_, {dyn; rand=(Config.Rand [unitr])}, _) as h)::t 
              when (if const_only then dyn = Config.Const else true) -> 
              if !unita = None
              then (unita := Some unitr; helper t)
              else if Utils.extract !unita = unitr
              then helper t 
              else 
                let witness = make_witness h path in 
                raise (err ~msg:msg1 ~witness)
            | (Cpo.Assign (_, _, {dyn; rand=(Config.Rand _)}, _) as h)::t
            | (Cpo.Declare (_, {dyn; rand=(Config.Rand _)}, _) as h)::t 
               when (if const_only then dyn = Config.Const else true) -> 
              let msg = "Multiple units of randomization." in 
              let witness = make_witness h path in 
              raise (err ~msg ~witness)
            | _::t -> helper t in 
            helper path in 
          List.for_all check_assumption_path prog        
        end

  let no_time_variance prog = object

      val err = make_assumption_error ~name:"no_time_variance"

      method check_assumption = 
        let open Config in 
        let rec check_assumption_path path = match path with 
          | [] -> true 
          | (Cpo.Declare (_, {Cpo.dyn=Tv}, _) as h)::_ -> 
            let msg = "Time varying treatment." in 
            let witness = make_witness h path in 
            raise (err ~msg ~witness)
          | _::t -> check_assumption_path t in 
        List.for_all check_assumption_path prog 
    end


end