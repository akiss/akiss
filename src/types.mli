type visi_type = Public | Hidden
type chanId = { name : string; visibility : visi_type; }
val null_chan : chanId
type funId = { name : string; arity : int; }
type typ = TermType | ChanType | Unknown
val show_typ : typ ref -> string
type argId = { name : string; th : int; }
type relative_location = int * string option
type relative_nonce = int * string
type relative_temp_term =
    F of funId * relative_temp_term list
  | Xor of relative_temp_term list
  | Z
  | T of int * relative_temp_term list
  | P of int * int * relative_temp_term
  | N of relative_nonce
  | V of relative_location
  | A of argId
  | C of chanId
type bounded_process =
    NilB
  | NameB of relative_nonce * bounded_process
  | InputB of relative_temp_term * relative_location * bounded_process
  | OutputB of relative_temp_term * relative_location * relative_temp_term *
      bounded_process
  | TestIfB of relative_location * relative_temp_term * relative_temp_term *
      bounded_process * bounded_process
  | ParB of bounded_process list
  | ChoiceB of relative_location * bounded_process list
  | CallB of relative_location * int * procId * relative_temp_term list
  | PhaseB of int * bounded_process
and procId = {
  name : string;
  arity : int;
  types : typ ref array;
  mutable process : bounded_process;
  mutable nbloc : int;
  mutable nbnonces : int;
}
val show_procId : procId -> string
val show_bounded_process : bounded_process -> string
val show_relative_term : relative_temp_term -> string
val show_relative_term_list : relative_temp_term list -> string
type statement_role = Master | Slave | New | Rule | Extra of int
val show_binder : statement_role -> string
type varId = { n : int; status : statement_role ref; }
type nonceId = { name : string; n : int; }
val null_nonce : nonceId
type io = Input of chanId | Output of chanId * term | Choice | Call
and location = {
  p : int;
  io : io;
  name : string;
  phase : int;
  observable : visi_type;
  parent : location option;
  parent_choices : location list;
}
and funName =
    Regular of funId
  | Nonce of nonceId
  | Plus
  | Zero
  | Tuple of int
  | Projection of int * int
  | Frame of location
  | InputVar of location
and funInfos = { id : funName; has_variables : bool; }
and term = Fun of funInfos * term list | Var of varId
val null_location : location
val root_location : int -> location
val show_varId : varId -> string
val show_term : term -> string
val show_term_list : term list -> string
val zero : term
type rewrite_rule = {
  binder_rule : statement_role ref;
  nbvars_rule : int;
  lhs : term;
  rhs : term;
}
val show_rewrite_rule : rewrite_rule -> string
type subst_lst = (varId * term) list
val show_subst_lst : (varId * term) list -> string
type subst_array = term option array
type subst_extra = {
  binder_extra : statement_role ref;
  nb_extra : int;
  subst_extra : subst_array;
}
type subst_maker = {
  m : subst_array;
  s : subst_array;
  e : subst_extra list;
}
val show_subst_maker : subst_maker -> string
type substitution = {
  binder : statement_role ref;
  nbvars : int;
  slave : term array;
  master : term array;
}
val show_substitution : substitution -> string
