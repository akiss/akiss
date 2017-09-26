val apply_subst_inputs : Types.term -> Inputs.inputs -> Types.term
val run_until_io :
  Process.process -> 'a -> Inputs.inputs -> ('a * Process.process) list
val init_run : Base.raw_statement -> Process.process -> Bijection.partial_run
val next_partial_run :
  Bijection.partial_run ->
  Dag.Dag.key ->
  Process.process ->
  Process.process ->
  Types.location ->
  Inputs.inputs -> Dag.LocationSet.t -> Bijection.partial_run
val apply_frame : Types.term -> Bijection.partial_run -> Types.term
val try_run :
  Bijection.partial_run ->
  Dag.Dag.key -> Dag.LocationSet.t * Process.process -> unit
val next_run : Bijection.partial_run -> Dag.LocationSet.elt
val statement_to_tests :
  Base.statement ->
  Process.process ->
  Bijection.solutions Bijection.Tests.t ->
  Bijection.solutions Bijection.Tests.t
val statements_to_tests :
  Base.statement ->
  Process.process ->
  Bijection.solutions Bijection.Tests.t ->
  Bijection.solutions Bijection.Tests.t
val base_to_tests :
  Base.base -> Process.process -> Bijection.solutions Bijection.Tests.t
val next_solution : Bijection.solutions -> unit
val find_possible_run :
  Bijection.solutions -> Bijection.partition list option
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
