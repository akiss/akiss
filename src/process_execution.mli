val apply_subst_inputs : Types.term -> Inputs.inputs -> Types.term
val run_until_io :
  Process.process ->
  'a ->
  Inputs.inputs ->
  (Inputs.choices * 'a * (Types.term * Types.term) list * Process.process)
  list * (Inputs.choices * 'a * 'b list * Process.process) list
val init_sol :
  'a ->
  Base.raw_statement ->
  Process.process -> Bijection.Run.test -> Bijection.Run.solution
val next_partial_run :
  Bijection.Run.partial_run ->
  Dag.LocationSet.elt ->
  Process.process ->
  Process.process ->
  Dag.Dag.key ->
  Inputs.inputs ->
  Dag.LocationSet.t ->
  Inputs.choices ->
  (Types.term * Types.term) list -> Bijection.Run.partial_run
val apply_frame : Types.term -> Bijection.Run.partial_run -> Types.term
val try_run :
  Bijection.Run.partial_run ->
  Dag.Dag.key ->
  Inputs.choices * Dag.LocationSet.t * (Types.term * Types.term) list *
  Process.process -> (Bijection.Run.partial_run * Types.location) option
val next_run_with_action :
  Dag.Dag.key ->
  Bijection.Run.partial_run -> Bijection.Run.partial_run list * Dag.Dag.key
val next_run :
  Bijection.Run.partial_run ->
  Bijection.Run.partial_run list * Types.location
val compatible :
  Bijection.correspondance ->
  Bijection.correspondance -> Dag.Dag.key -> Dag.Dag.key -> bool
val compatible_prun :
  Bijection.correspondance ->
  Bijection.correspondance -> Bijection.Run.partial_run -> bool
val get_all_new_roots :
  Dag.LocationSet.t ->
  Dag.LocationSet.t ->
  Bijection.Run.partial_run ->
  (Dag.LocationSet.t * Dag.LocationSet.t * Bijection.Run.partial_run) list
val check_recipes :
  Bijection.Run.partial_run -> Types.term * Types.term -> bool
val check_identities : Bijection.Run.partial_run -> Base.test_head -> bool
val next_solution : Bijection.Run.solution -> unit
val find_possible_run :
  Bijection.Run.solution -> Bijection.Solutions.elt option
