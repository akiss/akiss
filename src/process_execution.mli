val merge_tests :
  Base.raw_statement -> Base.raw_statement -> Base.raw_statement list
val apply_subst_inputs : Types.term -> Inputs.inputs -> Types.term
val run_until_io :
  Process.process ->
  'a ->
  Inputs.inputs ->
  (Inputs.choices * 'a * Process.process) list *
  (Inputs.choices * 'a * Process.process) list
val init_run :
  'a ->
  Base.raw_statement ->
  Process.process -> Bijection.test -> Bijection.partial_run
val next_partial_run :
  Bijection.partial_run ->
  Dag.LocationSet.elt ->
  Process.process ->
  Process.process ->
  Dag.Dag.key ->
  Inputs.inputs ->
  Dag.LocationSet.t -> Inputs.choices -> Bijection.partial_run
val apply_frame : Types.term -> Bijection.partial_run -> Types.term
val try_run :
  Bijection.partial_run ->
  Dag.Dag.key ->
  Inputs.choices * Dag.LocationSet.t * Process.process ->
  Bijection.partial_run list
val next_run :
  Bijection.partial_run -> Bijection.partial_run list * Dag.LocationSet.elt
val same_term_same_recipe : Base.raw_statement -> Base.raw_statement
val statement_to_tests :
  Bijection.which_process ->
  Bijection.origin -> Base.raw_statement -> Process.process -> unit
val statements_to_tests :
  Bijection.which_process -> Base.statement -> Process.process -> unit
val base_to_tests :
  Bijection.which_process -> Base.base -> Process.process -> unit
val check_recipes : Bijection.partial_run -> Types.term * Types.term -> bool
val next_solution : Bijection.solutions -> unit
val find_all_run : Bijection.solutions -> unit
exception Attack
val get_lst_of_test : Base.predicate -> (Types.term * Types.term) list
val add_merged_tests : Bijection.partial_run * Bijection.RunSet.t -> unit
val find_possible_run : Bijection.solutions -> Bijection.partial_run option
val equivalence : Types.procId -> Types.procId -> unit
