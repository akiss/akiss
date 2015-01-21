(** Compatibility with systems without Nproc *)

module Lwt = struct
  let return x = x
  let bind x f = f x
  let (>>=) = bind
  let wrap1 x = x
end

module Nproc = struct
  let create n = (), ()
  let submit () f x = try Some (f x) with _ -> None
end

module Lwt_unix = struct
  let run x = x
end

module Lwt_list = struct
  let map_p = List.map
  let filter_p = List.filter
end
