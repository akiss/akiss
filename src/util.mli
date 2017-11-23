exception Bug
val bench : float ref
val bench_cur : float ref
val bench_start : unit -> unit
val bench_stop : unit -> unit
val debug_output : bool ref
val verbose_output : bool ref
val about_seed : bool ref
val debug_seed : bool ref
val about_saturation : bool ref
val debug_saturation : bool ref
val about_tests : bool ref
val debug_tests : bool ref
val about_else : bool ref
val debug_else : bool ref
val about_execution : bool ref
val debug_execution : bool ref
val about_theory : bool ref
val debug_theory : bool
val about_traces : bool ref
val about_maude : bool ref
val about_canonization : bool ref
val about_progress : bool ref
val about_location : bool ref
val normalOutput : ('a, Format.formatter, unit) format -> 'a
val trmap : ('a -> 'b) -> 'a list -> 'b list
val union : 'a list list -> 'a list
val unique : 'a list -> 'a list
val create_list : 'a -> int -> 'a list
val create_consecutive : int -> int -> int list
val combine : 'a list -> 'b list -> ('a * 'b) list
val list_diff : 'a list -> 'a list -> 'a list
val list_intersect : 'a list -> 'a list -> 'a list
val is_prefix : 'a list -> 'a list -> bool
val iterate : ('a -> 'a) -> 'a -> 'a
val iterate_n : int -> ('a -> 'a) -> 'a -> 'a
val take : int -> 'a list -> 'a list
val all_prefixes : 'a list -> 'a list list
val show_string_list : string list -> string
val output_string : Format.formatter -> string -> unit
val pp_list :
  (Format.formatter -> 'a -> unit) ->
  string -> Format.formatter -> 'a list -> unit
