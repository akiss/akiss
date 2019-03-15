val verbose_execution : bool ref
(*val apply_subst_inputs : Types.term -> Inputs.inputs -> Types.term
val dispatch :
  ('a list * 'b list * 'c list) list -> 'a list * 'b list * 'c list
val run_until_io :
  Process.process ->
  Inputs.choices ->
  Dag.LocationSet.t ->
  Inputs.inputs ->
  (Types.location * Types.term option * Base.chankey * Bijection.extra_thread)
  list * Bijection.extra_thread list * Bijection.extra_thread list
val reduc_and_run :
  Dag.Dag.key ->
  Dag.Dag.key ->
  Types.term ->
  Bijection.extra_thread ->
  Bijection.extra_thread ->
  Inputs.inputs ->
  (Types.location * Types.term option * Base.chankey * Bijection.extra_thread)
  list * Bijection.extra_thread list * Bijection.extra_thread list
val merge_pending_lst :
  ('a * 'b * 'c) list Base.ChanMap.t ->
  ('a * 'b * Base.ChanMap.key * 'c) list ->
  ('a * 'b * 'c) list Base.ChanMap.t
val test_reduc_for_one :
  Dag.Dag.key * Types.term option * Base.chankey * Bijection.extra_thread ->
  Base.chankey ->
  (Dag.Dag.key * Types.term option * Bijection.extra_thread) list ->
  (Types.location * Types.term option * Bijection.extra_thread) list
  Base.ChanMap.t ->
  Inputs.inputs ->
  (Types.location * Types.term option * Base.chankey * Bijection.extra_thread)
  list * Bijection.extra_thread list * Bijection.extra_thread list
val test_all_internal_communications :
  (Types.location * Types.term option * Bijection.extra_thread) list
  Base.ChanMap.t ->
  (Types.location * Types.term option * Base.chankey * Bijection.extra_thread)
  list ->
  Inputs.inputs ->
  (Types.location * Types.term option * Base.chankey * Bijection.extra_thread)
  list * Bijection.extra_thread list * Bijection.extra_thread list
val run_silent_actions :
  Process.process ->
  (Types.location * Types.term option * Bijection.extra_thread) list
  Base.ChanMap.t ->
  Dag.LocationSet.t ->
  Inputs.inputs ->
  (Types.location * Types.term option * Base.chankey * Bijection.extra_thread)
  list * Bijection.extra_thread list * Bijection.extra_thread list *)
val dag_to_sequence : Dag.dag -> Types.location list
val init_sol :
  'a ->
  Base.raw_statement ->
  Process.process -> Types.location list -> Bijection.Test.test -> Bijection.Run.solution
val next_partial_run :
  Bijection.Run.partial_run ->
  Dag.LocationSet.elt ->
  Process.process ->
  Process.process ->
  Dag.Dag.key ->
  Inputs.inputs ->
  Dag.LocationSet.t -> Inputs.choices -> Bijection.Run.partial_run
val apply_frame : Types.term -> Bijection.Run.partial_run -> Types.term
(*val try_run :
  Bijection.Run.partial_run ->
  Types.location ->
  Bijection.extra_thread ->
  (Bijection.Run.partial_run * Types.location) option
val next_run_with_action :
  Types.location ->
  Bijection.Run.partial_run ->
  Bijection.Run.partial_run list * Types.location
val next_run :
  Bijection.Run.partial_run ->
  Bijection.Run.partial_run list * Types.location
val compatible :
  Bijection.correspondance ->
  Bijection.correspondance -> Dag.Dag.key -> Types.location -> bool
val compatible_prun :
  Bijection.correspondance ->
  Bijection.correspondance -> Bijection.Run.partial_run -> bool
val get_all_new_roots :
  Dag.LocationSet.t ->
  Dag.LocationSet.t ->
  Dag.dag -> (Dag.LocationSet.t * Dag.LocationSet.t) list
val check_recipes :
  Bijection.Run.partial_run -> Types.term * Types.term -> bool*)
val check_identities : Bijection.Run.partial_run -> Base.test_head -> bool 
val next_solution : Bijection.Run.solution -> unit
val find_possible_run :
  Bijection.Run.solution -> Bijection.Solutions.elt option
