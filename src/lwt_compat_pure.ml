(** Compatibility with systems without Nproc *)

module Lwt = struct
  let return x = x
  let bind x f = f x
  let (>>=) = bind
  let wrap1 x = x
end

module Nproc = struct
  let create n =
    if n > 1 then
      Printf.eprintf "[warn] This version of akiss is compiled without parallel computation support!\n%!";
    (), ()
  let submit () f x =
    try Some (f x)
    with e ->
      Printexc.print_backtrace stderr;
      Printf.eprintf
        "[err] Exception raised by task: %s\n"
        (Printexc.to_string e);
      None
end

module Lwt_main = struct
  let run x = x
end

module Lwt_list = struct
  let rev_map_p = List.rev_map
  let filter_p = List.filter

  let rec filter_map_p f l =
    match l with
    | [] -> []
    | hd :: tl ->
      match f hd with
      | None -> filter_map_p f tl
      | Some(e) -> e :: filter_map_p f tl
end
