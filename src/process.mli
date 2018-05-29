type action =
    Input of Types.location
  | Output of Types.location * Types.term
  | OutputA of Types.location * Types.term
  | Test of Types.term * Types.term
  | TestInequal of Types.term * Types.term
type process =
    EmptyP
  | ParallelP of process list
  | SeqP of action * process
  | ChoiceP of Types.location * (int * process) list
  | CallP of Types.location * Types.procId * Types.term array *
      Types.chanId array
type process_infos = { first_location : int; first_nonce : int; }
type processes_infos = {
  mutable next_location : int;
  mutable next_nonce : int;
  mutable processes : process_infos Dag.Dag.t;
  mutable location_list : Types.location list;
}
val processes_infos : processes_infos
val show_action : action -> string
val show_process : process -> string
val show_process_start : int -> process -> string
val count_type_nb : Types.typ -> Types.procId -> int -> int
val convert_term :
  Types.procId ->
  Types.location array ->
  Types.nonceId array ->
  Types.term array -> Types.relative_temp_term -> Types.term
val convert_chan :
  Types.procId ->
  Types.chanId array -> Types.relative_temp_term -> Types.chanId
val new_location :
  Types.procId ->
  int -> Types.io -> string -> Types.location option -> Types.location
val convert_pr :
  Types.procId * int * int * Types.location array * Types.nonceId array *
  Types.term array * Types.chanId array ->
  Types.bounded_process -> Types.location option -> process
val expand_call :
  Dag.Dag.key ->
  Types.procId -> Types.term array -> Types.chanId array -> process
