val negate_statement : Base.raw_statement -> Base.raw_statement
val statement_to_completion :
  Bijection.which_process -> Base.raw_statement -> Bijection.Run.completion
val same_term_same_recipe :
  Base.raw_statement -> Types.substitution * Base.raw_statement
val merge_tests :
  Bijection.which_process ->
  Base.raw_statement ->
  Base.raw_statement -> (Types.substitution * Base.raw_statement) list
val actual_test : Bijection.which_process -> Base.raw_statement -> bool
val map_dag : Dag.dag -> Bijection.correspondance -> Dag.dag
val apply_frame_2 :
  Types.substitution -> Types.term -> Bijection.Run.partial_run -> Types.term
val transpose_inputs :
  Types.substitution ->
  Inputs.inputs -> Bijection.Run.partial_run -> Inputs.inputs
val transpose_recipe :
  Types.substitution -> Types.term -> Bijection.Run.partial_run -> Types.term
val transpose_recipes :
  Types.substitution ->
  Inputs.inputs -> Bijection.Run.partial_run -> Inputs.inputs
val conj :
  Bijection.Run.partial_run -> Types.substitution * Base.raw_statement
val try_other_runs :
  Base.test_head -> Bijection.Run.solution -> Bijection.Solutions.elt option
val add_identities_to_completions :
  Base.test_head ->
  Bijection.which_process -> Bijection.Run.completion -> unit
val complete_set_of_identities :
  Base.test_head -> Bijection.which_process -> Bijection.Run.test -> unit
val statement_to_tests :
  Bijection.which_process ->
  Bijection.Run.origin ->
  Base.raw_statement -> Process.process -> Bijection.Run.test option
val add_merged_tests : Bijection.Solutions.elt -> unit
val find_set_of_runs : Bijection.Run.test -> unit
val completion_to_test : Bijection.Run.completion -> unit
val add_to_completion :
  Bijection.Run.partial_run -> Bijection.Run.completion -> unit
val compute_new_completions : Bijection.which_process -> unit
val statements_to_tests :
  Bijection.which_process ->
  Base.statement -> Process.process -> Base.EqualitiesSet.t -> unit
val base_to_tests :
  Bijection.which_process -> Base.base -> 'a -> Process.process -> unit
val equivalence : Types.procId -> Types.procId -> unit
