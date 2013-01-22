
module type T = sig

  type t
  type elt

  val create : unit -> t
  val add : elt -> t -> unit

  val next_not_solved : t -> (elt*elt) option
  val next_solved : t -> (elt*elt) option

  module S : Set.S with type elt = elt

  val solved : t -> S.t
  val not_solved : t -> S.t

  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_solved : (elt -> 'a -> 'a) -> t -> 'a -> 'a

  val only_solved : t -> elt list

end

module type O = sig
  type t
  val compare : t -> t -> int
  val is_solved : t -> bool
end

module Make (M:O) : T with type elt = M.t = struct

  module S = Set.Make(M)

  type elt = M.t

  type t = {
    mutable solved : S.t ;
    mutable not_solved : S.t ;
    s_todo : (elt*elt) Queue.t ;
    ns_todo : (elt*elt) Queue.t
  }

  let create () = {
    solved = S.empty ; not_solved = S.empty ;
    s_todo = Queue.create () ; ns_todo = Queue.create ()
  }

  let new_pair queue pair = Queue.push pair queue

  let next_not_solved kb =
    try Some (Queue.take kb.ns_todo) with Queue.Empty -> None

  let next_solved kb =
    try Some (Queue.take kb.s_todo) with Queue.Empty -> None

  let add x kb =
    if M.is_solved x then begin
      kb.solved <- S.add x kb.solved ;
      S.iter (fun y -> new_pair kb.s_todo (x,y)) kb.solved ;
      S.iter (fun y -> new_pair kb.ns_todo (x,y)) kb.not_solved
    end else begin
      kb.not_solved <- S.add x kb.not_solved ;
      S.iter (fun y -> new_pair kb.ns_todo (y,x)) kb.solved
    end

  let fold f kb x =
    S.fold f kb.not_solved (S.fold f kb.solved x)

  let fold_solved f kb x =
    S.fold f kb.solved x

  let only_solved kb = S.elements kb.solved

  let solved kb = kb.solved
  let not_solved kb = kb.not_solved

end
