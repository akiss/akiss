
let maude_command =
  let home = Sys.getenv "HOME" in
  let maude_dir = Filename.concat home "/soft/maude" in
  let maude = Filename.concat maude_dir "maude" in
  let full_maude = Filename.concat maude_dir "full-maude.maude" in
    maude ^ " -batch -no-banner -no-ansi-color " ^ full_maude

let tamarin_binary =
  try
    let path = Str.split (Str.regexp ":") (Sys.getenv "PATH") in
      List.find
        Sys.file_exists
        (List.map (fun d -> Filename.concat d "tamarin-prover") path)
  with
    | Not_found ->
        Printf.eprintf "Cound not find tamarin-prover in PATH!\n" ;
        Printf.eprintf "You may need to add something like \
                        ~/.cabal/bin to it.\n" ;
        exit 1

let maude_binary =
  try
    let path = Str.split (Str.regexp ":") (Sys.getenv "PATH") in
      List.find
        Sys.file_exists
        (List.map (fun d -> Filename.concat d "maude") path)
  with
    | Not_found ->
        Printf.eprintf "Cound not find maude in PATH!\n" ;
        Printf.eprintf "It is likely that tamarin-prover won't work.\n" ;
        exit 1
