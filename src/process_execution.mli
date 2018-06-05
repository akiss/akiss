val apply_subst_inputs : Types.term -> Inputs.inputs -> Types.term
val run_until_io :
  Process.process ->
  'a ->
  Inputs.inputs ->
  (Inputs.choices * 'a * (Types.term * Types.term) list * Process.process)
  list * (Inputs.choices * 'a * 'b list * Process.process) list
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
  Dag.LocationSet.t ->
  Inputs.choices -> (Types.term * Types.term) list -> Bijection.partial_run
val apply_frame : Types.term -> Bijection.partial_run -> Types.term
val try_run :
  Bijection.partial_run ->
  Dag.Dag.key ->
  Inputs.choices * Dag.LocationSet.t * (Types.term * Types.term) list *
  Process.process -> (Bijection.partial_run * Types.location) option
val next_run_with_action :
  Dag.Dag.key ->
  Bijection.partial_run -> Bijection.partial_run list * Dag.Dag.key
val next_run :
  Bijection.partial_run -> Bijection.partial_run list * Types.location
val same_term_same_recipe : Base.raw_statement -> Base.raw_statement
val compatible :
  Bijection.correspondance ->
  Bijection.correspondance -> Dag.Dag.key -> Dag.Dag.key -> bool
val compatible_prun :
  Bijection.correspondance ->
  Bijection.correspondance -> Bijection.partial_run -> bool
val get_all_new_roots :
  Dag.LocationSet.t ->
  Bijection.partial_run -> (Types.location * Bijection.partial_run) list
val check_recipes : Bijection.partial_run -> Types.term * Types.term -> bool
val next_solution : Bijection.solutions -> Bijection.partial_run list option
val find_possible_run :
  Bijection.solutions -> Bijection.partial_run list option
val find_compatible_run :
  Bijection.solutions -> Bijection.Solutions.elt list option
