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
  bool ->
  Bijection.partial_run ->
  Dag.Dag.key ->
  Inputs.choices * Dag.LocationSet.t * (Types.term * Types.term) list *
  Process.process -> (Bijection.partial_run * Types.location) option
val next_run :
  bool ->
  Bijection.partial_run -> Bijection.partial_run list * Dag.LocationSet.elt
val same_term_same_recipe : Base.raw_statement -> Base.raw_statement
val statement_to_tests :
  Bijection.which_process ->
  Bijection.origin -> Base.raw_statement -> Process.process -> unit
val statements_to_tests :
  Bijection.which_process -> Base.statement -> Process.process -> unit
val base_to_tests :
  Bijection.which_process -> Base.base -> Process.process -> unit
val compatible :
  Bijection.correspondance ->
  Bijection.correspondance -> Dag.Dag.key -> Dag.Dag.key -> bool
val compatible_prun :
  Bijection.correspondance ->
  Bijection.correspondance -> Bijection.partial_run -> bool
val check_recipes : Bijection.partial_run -> Types.term * Types.term -> bool
val next_solution : Bijection.solutions -> unit
val next_solution_else : Bijection.solutions -> unit
val find_all_run : Bijection.solutions -> Bijection.Solutions.t
val transpose : Types.term -> Bijection.correspondance -> Types.term
val apply_var_set_pred :
  Base.predicate ->
  Types.term Term.VarMap.t -> Bijection.correspondance -> Base.predicate
val refine_recipes :
  Base.raw_statement ->
  Base.raw_statement -> Bijection.correspondance -> Base.raw_statement
val find_compatible_run :
  Bijection.solutions -> Bijection.Solutions.elt option
