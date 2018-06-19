val recipes_of_head :
  Base.predicate -> Base.EqualitiesSet.t * Base.EqualitiesSet.t
val head_predicate_to_test : Base.predicate -> Base.predicate
type which_process = P | Q
val show_which_process : which_process -> string
type correspondance = { a : Types.location Dag.Dag.t; }
val empty_correspondance : correspondance
val is_empty_correspondance : correspondance -> bool
val show_correspondance : correspondance -> string
val canonize_correspondance : correspondance -> correspondance
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
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
  end
val show_int_set : IntegerSet.t -> string
module rec Run :
  sig
    type completion = {
      st_c : Base.raw_statement;
      corresp_c : correspondance;
      corresp_back_c : correspondance;
      core_corresp : (Types.location * Types.location) list;
      missing_actions : Dag.LocationSet.t;
      selected_action : Types.location;
      root : complement_root;
      mutable further_completions : (Types.substitution * completion) list;
      mutable generated_test : (Types.substitution * test) option;
    }
    and complement_root = {
      from_base : which_process;
      initial_statement : Base.raw_statement;
      mutable directory : completion list Dag.Dag.t;
    }
    and partial_run = {
      test : test;
      sol : solution;
      corresp : correspondance;
      corresp_back : correspondance;
      remaining_actions : Dag.LocationSet.t;
      frame : Inputs.inputs;
      choices : Inputs.choices;
      disequalities : (Types.term * Types.term) list;
      qthreads :
        (Inputs.choices * Dag.LocationSet.t *
         (Types.term * Types.term) list * Process.process)
        list;
      failed_qthreads :
        (Inputs.choices * Dag.LocationSet.t *
         (Types.term * Types.term) list * Process.process)
        list;
      restrictions : Dag.LocationSet.t;
      parent : partial_run option;
      last_exe : Types.location;
      weird_assoc : int;
      score : int;
      mutable consequences :
        (Types.statement_role * Types.substitution * test) list;
      mutable completions : (Types.substitution * completion) list;
    }
    and origin =
        Initial of Base.statement
      | Composed of partial_run * partial_run
      | Completion
      | Temporary
    and test = {
      process_name : which_process;
      statement : Base.raw_statement;
      origin : origin;
      id : int;
      from : IntegerSet.t;
      nb_actions : int;
      mutable new_actions : int;
      mutable constraints : correspondance;
      mutable constraints_back : correspondance;
      mutable solutions_todo : solution list;
      mutable solutions_done : solution list;
    }
    and solution = {
      init_run : partial_run;
      mutable partial_runs : partial_run list;
      mutable partial_runs_todo : Solutions.t;
      mutable possible_runs_todo : Solutions.t;
      mutable possible_runs : Solutions.t;
      mutable movable : int;
      mutable restricted_dag : Dag.dag;
      mutable selected_run : partial_run option;
      sol_test : test;
    }
    type t = partial_run
    val show_run : partial_run -> string
    val show_partial_run : partial_run -> string
    val show_origin : origin -> string
    val show_test : test -> string
    val show_completion : completion -> string
    val show_all_completions : completion list Dag.Dag.t -> unit
    val compare : t -> t -> int
  end
and Solutions :
  sig
    type elt = Run.t
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
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
  end
module PartialRun :
  sig
    type t = Run.partial_run
    val compare : Run.partial_run -> Run.partial_run -> int
  end
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
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
  end
module Test :
  sig type t = Run.test val compare : Run.test -> Run.test -> int end
module Tests :
  sig
    type elt = Test.t
    type t = Set.Make(Test).t
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
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
  end
exception Attack of Run.test * Run.solution
val null_test : Run.test
val null_sol : Run.solution
val empty_run : Run.partial_run
type record = {
  locP : Types.location;
  locQ : Types.location;
  partial_run : Run.partial_run;
}
type index = RunSet.t Dag.Dag.t Dag.Dag.t
type bijection = {
  mutable p : Process.process;
  mutable q : Process.process;
  mutable satP : Base.base;
  mutable satQ : Base.base;
  mutable indexP : index;
  mutable indexQ : index;
  mutable next_id : int;
  mutable tests : Tests.t;
  mutable registered_tests : Tests.t;
  mutable runs_for_completions_P : Run.partial_run list;
  mutable runs_for_completions_Q : Run.partial_run list;
  mutable partial_completions_P : Run.completion list Dag.Dag.t;
  mutable partial_completions_Q : Run.completion list Dag.Dag.t;
  mutable todo_completion_P : Run.completion list;
  mutable todo_completion_Q : Run.completion list;
  mutable locs : Dag.LocationSet.t;
  htable_st : (Base.hash_test, Run.test) Hashtbl.t;
}
val bijection : bijection
val show_bijection : unit -> unit
val show_hashtbl : unit -> unit
val proc : which_process -> Process.process
val other : which_process -> which_process
val reorder_int_set : IntegerSet.t -> IntegerSet.t
val push :
  Base.raw_statement ->
  which_process -> Run.origin -> (Run.test -> Run.solution) -> Run.test
val reorder_tests : unit -> unit
val pop : unit -> Tests.elt
val register_completion : Run.completion -> bool
exception LocPtoQ of int
val loc_p_to_q : Dag.Dag.key -> correspondance -> Types.location
val add_run : RunSet.elt -> unit
val remove_run : RunSet.elt -> unit
val mappings_of : which_process -> Dag.Dag.key -> RunSet.t Dag.Dag.t
val mapping_exists : which_process -> Dag.Dag.key -> Dag.Dag.key -> bool
val straight : which_process -> Dag.Dag.key -> Dag.Dag.key -> bool
val compatible : Run.partial_run -> RunSet.t
