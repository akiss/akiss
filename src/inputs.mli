exception Incompatible_choices
type inputs = { i : Types.term Dag.Dag.t; }
type choices = { c : int Dag.Dag.t; }
val show_inputs : inputs -> string
val show_choices : choices -> string
val show_verbose_choices : choices -> unit
val new_inputs : inputs
val new_choices : choices
type hash_inputs 
type hash_choices = (int * int) list
val inputs_to_hash : inputs -> hash_inputs
val choices_to_hash : choices -> hash_choices
val add_input : Dag.Dag.key -> Types.varId -> inputs -> inputs
val add_choice : Dag.Dag.key -> int -> choices -> choices
val add_to_frame : Dag.Dag.key -> Types.term -> inputs -> inputs
val get_output_of_input : choices -> Dag.Dag.key -> Dag.Dag.key
val subset_choices : choices -> choices -> bool
val merge_choices : choices -> choices -> choices option
val merge_choices_add_link :
  choices -> choices -> Dag.Dag.key -> Dag.Dag.key -> choices option
val merge_choices_with_link :
  choices -> choices -> Dag.Dag.key -> Dag.Dag.key -> choices option
val get : Dag.Dag.key -> inputs -> Types.term
val get_choice_opt : Dag.Dag.key -> choices -> int option
val map : (Types.term -> Types.term) -> inputs -> inputs
val csu : Types.subst_maker -> inputs -> inputs -> Types.subst_maker list
val csu_recipes :
  Types.subst_maker -> inputs -> inputs -> Types.subst_maker list
val csm :
  bool -> Types.statement_role ref -> inputs -> inputs -> Types.subst_lst list
val csm_recipes :
  bool -> Types.statement_role ref -> inputs -> inputs -> Types.subst_lst list
val merge : Types.substitution -> inputs -> inputs -> inputs
val merge_recipes : Types.substitution -> inputs -> inputs -> inputs
val apply_subst_recipes : Types.substitution -> inputs -> inputs
val are_normal : inputs -> bool
val renormalize : inputs -> inputs
val contains : inputs -> inputs -> bool
