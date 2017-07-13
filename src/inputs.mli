type inputs = { i : Types.term Dag.Dag.t; }
val show_inputs : inputs -> string
val new_inputs : inputs
val add_input : 'a -> Dag.Dag.key -> Types.varId -> inputs -> inputs
val get : Dag.Dag.key -> inputs -> Types.term
val map : (Types.term -> Types.term) -> inputs -> inputs
val csu :
  Types.term option array * Types.term option array ->
  inputs ->
  inputs -> (Types.term option array * Types.term option array) list
val csm : inputs -> inputs -> (Types.varId * Types.term) list list
val merge : Types.substitution -> inputs -> inputs -> inputs