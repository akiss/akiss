type action =
    Input of Types.location
  | Output of Types.location * Types.term
  | Test of Types.term * Types.term
  | TestInequal of Types.term * Types.term
type process =
    EmptyP
  | ParallelP of process list
  | SeqP of action * process
  | CallP of Types.location * Types.procId * Types.term array *
      Types.chanId array
val show_action : action -> string
val show_process : process -> string
val count_type_nb : Types.typ -> Types.procId -> int -> int
val convert_term :
  Types.procId ->
  Types.location array ->
  Types.nonceId array ->
  Types.term array -> Types.relative_temp_term -> Types.term
val convert_chan :
  Types.procId ->
  Types.chanId array -> Types.relative_temp_term -> Types.chanId
val convert_pr :
  Types.procId * int * int * Types.location array * Types.nonceId array *
  Types.term array * Types.chanId array -> Types.bounded_process -> process
