open Term
open Process

(** {2 Executing and testing processes} *)

exception Process_blocked
exception Not_a_recipe
exception Bound_variable
exception Invalid_instruction
exception Too_many_instructions

val execute : trace -> term list -> term -> rules -> term list * action list

val is_reach_test : term -> bool
val is_ridentical_test : term -> bool
val trace_from_frame : term list -> trace
val restrict_frame_to_channels : term list -> trace -> id list -> term list
val check_test : trace -> trace -> term -> rules -> bool
val check_reach_tests : trace -> trace -> term list -> rules -> term option
val check_ridentical_tests : trace -> trace -> term list -> rules -> term option 
