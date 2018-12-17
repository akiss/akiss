val negate_statement : Base.raw_statement -> Base.raw_statement
val statement_to_completion :
  Bijection.which_process ->
  Base.statement -> Base.raw_statement -> Bijection.Run.completion
val merge_tests :
  Bijection.which_process ->
  Base.raw_statement ->
  Base.raw_statement -> (Types.substitution * Base.raw_statement) list
val actual_test : Bijection.which_process -> Base.raw_statement -> bool
val conj :
  Bijection.Run.partial_run -> Types.substitution * Base.raw_statement
val trunconj :
  Dag.LocationSet.t ->
  Bijection.Run.partial_run -> Types.substitution * Base.raw_statement
val try_other_runs :
  Base.test_head -> Bijection.Run.solution -> Bijection.Solutions.elt option
val statement_to_tests :
  Bijection.which_process ->
  Bijection.Run.origin ->
  Base.raw_statement -> Process.process -> Bijection.Test.test option
val add_merged_tests : Bijection.Solutions.elt -> unit
val find_set_of_runs : Bijection.Test.test -> unit
val completion_to_test : Bijection.Run.completion -> unit
val nb_comp : int ref
val add_to_completion :
  Bijection.Run.partial_run -> Bijection.Run.completion -> unit
val compute_new_completions : Bijection.which_process -> unit
val statements_to_tests :
  bool ->
  bool ->
  Bijection.which_process ->
  Base.statement -> Process.process -> Base.EqualitiesSet.t -> unit
val unreach_to_completion : Bijection.which_process -> Base.base -> unit
val base_to_tests :
  bool ->
  bool -> Bijection.which_process -> Base.base -> Process.process -> unit
val equivalence : bool -> Types.procId -> Types.procId -> unit
