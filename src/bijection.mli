type which_process = P | Q
type correspondance = { a : Types.location Dag.Dag.t; }
val show_correspondance : correspondance -> string
type partial_run = {
  process : which_process;
  statement : Base.raw_statement;
  corresp : correspondance;
  corresp_back : correspondance;
  remaining_actions : Dag.LocationSet.t;
  frame : Inputs.inputs;
  dag : Dag.dag;
  qthreads : (Dag.LocationSet.t * Process.process) list;
  mutable children : partial_run list;
}
val show_run : partial_run -> string
val show_partial_run : partial_run -> string
type test = { nb_actions : int; test : Base.statement; }
type solutions = {
  mutable partial_runs : partial_run list;
  mutable partial_runs_todo : partial_run list;
  mutable partial_runs_priority_todo : partial_run list;
  mutable possible_runs : partial_run list;
  mutable possible_runs_todo : partial_run list;
  mutable partitions : partial_run list;
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
type record = {
  locP : Types.location;
  locQ : Types.location;
  partial_run : partial_run;
}
type bijection = { mutable records : record list; }
val base : bijection
val show_base : unit -> unit
val loc_p_to_q : Dag.Dag.key -> correspondance -> Types.location
val add_partial_run : partial_run -> unit
val remove_partition : partial_run -> unit
val records_for_P : Types.location -> record list
val straight : Types.location -> Types.location -> bool
val compatible : partial_run -> partial_run list
