exception NotAnExperiment
 
module ClassificationFailures = struct 
    exception Interrupt of Core.Signal.t
end

module ToolFailures = struct
    exception NYI of string
    exception TooManyChoices of string * int 
end

module type Staticbug = sig 
    type node 
    type pi = node list 
    type cpo_expr 
    
    exception NotAnExperiment
    exception LoggedPathNoRandomization of pi
    exception UnloggedPathRandomization of pi 
    exception NoPaths
    exception UnreachableCode of node 
    exception UnitTupleNonUnique
    exception UnitLowCardinality of string
    exception GuardAlwaysFalse
    exception GuardAlwaysTrue
    exception NonUniqueChoicesRV of cpo_expr list 
    exception RandomVariableChoiceFailure of string * int
    exception ReturnNotStaticallyDecidable of string list
    exception RVNormalizationError of cpo_expr * cpo_expr 
    exception RVConcretizationError of cpo_expr * cpo_expr 
    exception InsufficientWeightInformation of cpo_expr 
    exception NoContrasts of string 
    exception PositivityError of string * cpo_expr 
    exception ConversionError of cpo_expr * string 
    exception CausalSufficiencyError of string 
    exception DataFlowDeterminism of cpo_expr
end 

module Make(Cpo : sig 
    type node 
    type pi = node list 
    type cpo_expr 
end) = struct
    include Cpo
    exception NotAnExperiment
    exception LoggedPathNoRandomization of pi
    exception UnloggedPathRandomization of pi 
    exception NoPaths
    exception UnreachableCode of node 
    exception UnitTupleNonUnique
    exception UnitLowCardinality of string
    exception GuardAlwaysFalse
    exception GuardAlwaysTrue
    exception NonUniqueChoicesRV of cpo_expr list 
    exception RandomVariableChoiceFailure of string * int
    exception ReturnNotStaticallyDecidable of string list
    exception RVNormalizationError of cpo_expr * cpo_expr 
    exception RVConcretizationError of cpo_expr * cpo_expr 
    exception InsufficientWeightInformation of cpo_expr 
    exception NoContrasts of string 
    exception PositivityError of string * cpo_expr 
    exception ConversionError of cpo_expr * string 
    exception CausalSufficiencyError of string     
    exception DataFlowDeterminism of cpo_expr
end