val merge_tests :
  Base.raw_statement -> Base.raw_statement -> Base.raw_statement list
exception Attack
val get_lst_of_test : Base.predicate -> (Types.term * Types.term) list
val map_dag : Dag.dag -> Bijection.correspondance -> Dag.dag
val transpose_inputs :
  Inputs.inputs -> Bijection.partial_run -> Inputs.inputs
val conj : Bijection.partial_run -> Base.raw_statement
val add_to_completion : Bijection.partial_run -> Bijection.completion -> unit
val negate_statement : Base.raw_statement -> Base.raw_statement
val statement_to_completion : Base.raw_statement -> Bijection.completion
val statement_to_tests :
  Bijection.which_process ->
  Bijection.origin -> Base.raw_statement -> Process.process -> unit
val statements_to_tests :
  Bijection.which_process -> Base.statement -> Process.process -> unit
val add_merged_tests : Bijection.possible_runs -> unit
val register_solution :
  Bijection.solutions -> Bijection.Solutions.elt -> unit
val find_compatible_run_init :
  Bijection.correspondance ->
  Bijection.correspondance -> Bijection.RunSet.elt -> bool
val compute_new_completions : Bijection.which_process -> unit
val base_to_tests :
  Bijection.which_process -> Base.base -> 'a -> Process.process -> unit
val equivalence : Types.procId -> Types.procId -> unit
