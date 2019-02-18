type ident = string * int
type temp_term =
    Id of ident
  | FuncApp of ident * temp_term list
  | Tuple of temp_term list
  | FPlus of temp_term * temp_term
  | FZero
type functions = Function of ident * int * bool
type pattern = PVar of ident | PTuple of pattern list | PTest of temp_term
type plain_process =
    Nil
  | Call of ident * temp_term list
  | Choice of plain_process * plain_process
  | Par of plain_process * plain_process
  | Bang of int * plain_process * int
  | New of ident * plain_process
  | In of ident * ident * plain_process
  | Out of ident * temp_term * plain_process
  | Let of pattern * temp_term * plain_process * plain_process
  | IfThenElse of temp_term * temp_term * plain_process * plain_process
  | Seq of plain_process * plain_process
  | Phase of int * plain_process
type extended_process = EPlain of plain_process
type query =
    Saturate of ident
  | Trace_Eq of bool * ident * ident
  | Obs_Eq of extended_process * extended_process
type extended2_process =
    ExtendedProcess of ident * ident list * extended_process
type declaration =
  | Latex of string
  | FuncDecl of functions list
  | ReducList of (temp_term * temp_term) list
  | FreeName of ident list
  | ChanNames of ident list
  | PrivateChanNames of ident list
  | Query of query * int
  | ProcessDecl of extended2_process
type env_elt =
    Var of Types.relative_location
  | XVar of Types.varId
  | Name of Types.relative_nonce
  | Func of Types.funId
  | Chan of Types.chanId
  | Proc of Types.procId
  | ArgVar of Types.argId
  | PatVar of Types.relative_temp_term
module StringComp : sig type t = string val compare : 'a -> 'a -> int end
module Env :
  sig
    type key = StringComp.t
    type 'a t = 'a Map.Make(StringComp).t
    val find : key -> 'a t -> 'a
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val empty : 'a t
  end
val environment : env_elt Env.t ref 
val processes_list : extended2_process list ref
type symb_chan = Const of Types.chanId | Sym of Types.argId
val display_env_elt_type : env_elt -> string
val show_environment : env_elt Env.t -> string
val error_message : int -> string -> 'a
val warning_message : int -> string -> unit
val rewrite_rules : Types.rewrite_rule list ref
val rewrite_rule_proj : int -> unit
val rewrite_rule_xor_1 : Types.rewrite_rule
val rewrite_rule_xor_2 : Types.rewrite_rule
val rewrite_rule_xor_3 : Types.rewrite_rule
val parse_rewrite_rule :
  env_elt Env.t -> temp_term * temp_term -> Types.rewrite_rule
val functions_list : Types.funId list ref
val parse_functions : env_elt Env.t -> functions -> env_elt Env.t
val parse_free_name : env_elt Env.t -> Env.key * int -> env_elt Env.t
val parse_channel_name : env_elt Env.t -> Env.key * int -> env_elt Env.t
val parse_private_channel_name :
  env_elt Env.t -> Env.key * int -> env_elt Env.t
val parse_chan :
  Types.procId -> env_elt Env.t -> Env.key * int -> Types.relative_temp_term
val tuple_arity : int list ref
val use_xor : bool ref
val type_of_arg :
  Types.procId -> env_elt Env.t -> temp_term -> int * Types.typ
val parse_plain_process :
  Types.procId ->
  env_elt Env.t ->
  int * int -> plain_process -> int * int * Types.bounded_process
val parse_extended_process :
  Types.procId ->
  env_elt Env.t -> extended_process -> int * int * Types.bounded_process
val parse_list_argument :
  Types.procId ->
  extended_process ->
  env_elt Env.t ->
  int -> (Env.key * int) list -> int * int * Types.bounded_process
val get_process_name : extended2_process -> unit
val parse_process_declaration_list : extended2_process list -> unit
val nonces : (int * Types.nonceId) list ref
val frames : (int * Types.location) list ref
