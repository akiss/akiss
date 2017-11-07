type which_process = P | Q
type correspondance = { a : Types.location Dag.Dag.t; }
val show_correspondance : correspondance -> string
module IntegerSet :
  sig
    type elt = int
    type t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val of_list : elt list -> t
  end
type partial_run = {
  test : test;
  corresp : correspondance;
  corresp_back : correspondance;
  remaining_actions : Dag.LocationSet.t;
  frame : Inputs.inputs;
  choices : Inputs.choices;
  dag : Dag.dag;
  qthreads : (Inputs.choices * Dag.LocationSet.t * Process.process) list;
  failed_qthreads :
    (Inputs.choices * Dag.LocationSet.t * Process.process) list;
}
and origin = Initial of Base.statement | Composed of test * test
and test = {
  process_name : which_process;
  statement : Base.raw_statement;
  origin : origin;
  id : int;
  from : IntegerSet.t;
  nb_actions : int;
  new_actions : int;
}
val show_run : partial_run -> string
val show_partial_run : partial_run -> string
val show_origin : origin -> string
val show_test : test -> string
module PartialRun :
  sig type t = partial_run val compare : 'a -> 'a -> int end
module RunSet :
  sig
    type elt = PartialRun.t
    type t = Set.Make(PartialRun).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val of_list : elt list -> t
  end
type solutions = {
  mutable partial_runs : partial_run list;
  mutable partial_runs_todo : partial_run list;
  mutable partial_runs_priority_todo : partial_run list;
  mutable possible_runs : (partial_run * RunSet.t) list;
  mutable possible_restricted_runs : partial_run list;
  mutable possible_runs_todo : partial_run list;
  mutable failed_partial_run : partial_run list;
  mutable failed_run : partial_run list;
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
type record = {
  locP : Types.location;
  locQ : Types.location;
  partial_run : partial_run;
}
type index = RunSet.t Dag.Dag.t Dag.Dag.t
type bijection = {
  mutable p : Process.process;
  mutable q : Process.process;
  mutable indexP : index;
  mutable indexQ : index;
  mutable next_id : int;
  mutable tests : solutions Tests.t;
  mutable locs : Dag.LocationSet.t;
  htable : (IntegerSet.t, unit) Hashtbl.t;
}
val base : bijection
val show_base : unit -> unit
val proc : which_process -> Process.process
val other : which_process -> which_process
val push :
  Base.raw_statement ->
  which_process -> origin -> (test -> partial_run) -> unit
val pop : unit -> Tests.key * solutions
val loc_p_to_q : Dag.Dag.key -> correspondance -> Types.location
val add_partial_run : RunSet.elt -> unit
val remove_partition : 'a -> unit
val straight : Dag.Dag.key -> Dag.Dag.key -> bool
val compatible : partial_run -> RunSet.t
