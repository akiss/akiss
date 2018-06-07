val recipes_of_head :
  Base.predicate -> Base.EqualitiesSet.t * Base.EqualitiesSet.t
val merge_tests :
  Base.raw_statement -> Base.raw_statement -> Base.raw_statement list
exception Attack
val actual_test : Bijection.which_process -> Base.raw_statement -> bool
val map_dag : Dag.dag -> Bijection.correspondance -> Dag.dag
val apply_frame_2 :
  Types.substitution -> Types.term -> Bijection.partial_run -> Types.term
val transpose_inputs :
  Types.substitution ->
  Inputs.inputs -> Bijection.partial_run -> Inputs.inputs
val transpose_recipe : Types.term -> Bijection.partial_run -> Types.term
val transpose_recipes :
  Inputs.inputs -> Bijection.partial_run -> Inputs.inputs
val conj : Bijection.partial_run -> Base.raw_statement
val statement_to_tests :
  Bijection.which_process ->
  Bijection.origin -> Base.raw_statement -> Process.process -> unit
val completion_to_test : Bijection.completion -> unit
val add_to_completion : Bijection.partial_run -> Bijection.completion -> unit
val negate_statement : Base.raw_statement -> Base.raw_statement
val statement_to_completion :
  Bijection.which_process -> Base.raw_statement -> Bijection.completion
val statements_to_tests :
  Bijection.which_process -> Base.statement -> Process.process -> unit
val add_merged_tests : Bijection.partial_run -> unit
val register_solution :
  Bijection.solutions -> Bijection.Solutions.elt list -> unit
val find_compatible_run_init :
  Bijection.correspondance ->
  Bijection.correspondance -> Bijection.RunSet.elt -> bool
val compute_new_completions : Bijection.which_process -> unit
val base_to_tests :
  Bijection.which_process -> Base.base -> 'a -> Process.process -> unit
val equivalence : Types.procId -> Types.procId -> unit
