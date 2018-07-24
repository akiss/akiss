exception Incompatible_choices
type inputs = { i : Types.term Dag.Dag.t; }
type choices = { c : int Dag.Dag.t; }
val show_inputs : inputs -> string
val show_choices : choices -> string
val new_inputs : inputs
val new_choices : choices
val canonize_inputs : inputs -> inputs
val canonize_choices : choices -> choices
val add_input : Dag.Dag.key -> Types.varId -> inputs -> inputs
val add_choice : Dag.Dag.key -> int -> choices -> choices
val add_to_frame : Dag.Dag.key -> Types.term -> inputs -> inputs
val subset_choices : choices -> choices -> bool
val merge_choices : choices -> choices -> choices option
val merge_choices_add_link :
  choices -> choices -> Dag.Dag.key -> Dag.Dag.key -> choices option
val get : Dag.Dag.key -> inputs -> Types.term
val map : (Types.term -> Types.term) -> inputs -> inputs
val csu :
  Types.term option array * Types.term option array ->
  inputs ->
  inputs -> (Types.term option array * Types.term option array) list
val csu_recipes :
  Types.term option array * Types.term option array ->
  inputs ->
  inputs -> (Types.term option array * Types.term option array) list
val csm : inputs -> inputs -> (Types.varId * Types.term) list list
val merge : Types.substitution -> inputs -> inputs -> inputs
val merge_recipes : Types.substitution -> inputs -> inputs -> inputs
val apply_subst_recipes : Types.substitution -> inputs -> inputs
val are_normal : inputs -> bool
val contains : inputs -> inputs -> bool
val debug : inputs -> inputs -> int
