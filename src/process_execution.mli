val merge_tests :
  Base.raw_statement -> Base.raw_statement -> Base.raw_statement list
val apply_subst_inputs : Types.term -> Inputs.inputs -> Types.term
val run_until_io :
  Process.process -> 'a -> Inputs.inputs -> ('a * Process.process) list
val init_run :
  Bijection.which_process ->
  Base.raw_statement -> Process.process -> Bijection.partial_run
val next_partial_run :
  Bijection.partial_run ->
  Dag.Dag.key ->
  Process.process ->
  Process.process ->
  Dag.Dag.key -> Inputs.inputs -> Dag.LocationSet.t -> Bijection.partial_run
val apply_frame : Types.term -> Bijection.partial_run -> Types.term
val try_run :
  Bijection.partial_run ->
  Dag.Dag.key -> Dag.LocationSet.t * Process.process -> unit
val next_run : Bijection.partial_run -> Dag.LocationSet.elt
val statement_to_tests :
  Bijection.which_process ->
  Base.statement ->
  Process.process ->
  Bijection.solutions Bijection.Tests.t ->
  Bijection.solutions Bijection.Tests.t
val statements_to_tests :
  Bijection.which_process ->
  Base.statement ->
  Process.process ->
  Bijection.solutions Bijection.Tests.t ->
  Bijection.solutions Bijection.Tests.t
val base_to_tests :
  Bijection.which_process ->
  Base.base -> Process.process -> Bijection.solutions Bijection.Tests.t
val check_recipes : Bijection.partial_run -> Types.term * Types.term -> bool
val next_solution : Bijection.solutions -> unit
val find_possible_run :
  Bijection.solutions -> Bijection.partial_run list option
type equivalence = {
  processP : Process.process;
  processQ : Process.process;
  tracesP : Base.base;
  tracesQ : Base.base;
  mutable actions_P_to_Q : Bijection.correspondance;
  mutable actions_Q_to_P : Bijection.correspondance;
  testsP : Bijection.tests;
  testsQ : Bijection.tests;
}
val equivalence : Types.procId -> Types.procId -> unit
