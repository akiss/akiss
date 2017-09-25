type correspondance = { a : Types.location Dag.Dag.t; }
type status = Done | Fail | Full | Partial
type partial_run = {
  statement : Base.raw_statement;
  corresp : correspondance;
  remaining_actions : Dag.LocationSet.t;
  frame : Inputs.inputs;
  dag : Dag.dag;
  qthreads : (Dag.LocationSet.t * Process.process) list;
  mutable status : status;
  mutable children : partial_run list;
}
val show_correspondance : correspondance -> string
val show_partial_run : partial_run -> string
type test = { nb_actions : int; test : Base.raw_statement; }
type solutions = {
  mutable partial_runs : partial_run list;
  mutable partial_runs_todo : partial_run list;
  mutable possible_runs : partial_run list;
}
module Test : sig type t = test val compare : test -> test -> int end
module Tests :
  sig
    type key = Test.t
    type 'a t = 'a Map.Make(Test).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val max_binding : 'a t -> key * 'a
    val choose : 'a t -> key * 'a
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  end
type tests = { tests : solutions Tests.t; }
val apply_frame : Types.term -> Inputs.inputs -> Types.term
val run_until_io :
  Process.process -> 'a -> Inputs.inputs -> ('a * Process.process) list
val init_run : Base.raw_statement -> Process.process -> partial_run
val next_partial_run :
  partial_run ->
  Dag.Dag.key ->
  Process.process ->
  Process.process ->
  Types.location -> Inputs.inputs -> Dag.LocationSet.t -> partial_run
val try_run :
  partial_run -> Dag.Dag.key -> Dag.LocationSet.t * Process.process -> unit
val next_run : partial_run -> unit
val statement_to_tests :
  Base.raw_statement ->
  Process.process -> solutions Tests.t -> solutions Tests.t
val statements_to_tests :
  Base.statement -> Process.process -> solutions Tests.t -> solutions Tests.t
val base_to_tests : Base.base -> Process.process -> solutions Tests.t
val next_solution : solutions -> unit
val find_possible_run : solutions -> partial_run option
type equivalence = {
  processP : Process.process;
  processQ : Process.process;
  tracesP : Base.base;
  tracesQ : Base.base;
  mutable actions_P_to_Q : correspondance;
  mutable actions_Q_to_P : correspondance;
  testsP : tests;
  testsQ : tests;
}
val equivalence : Types.procId -> Types.procId -> unit
