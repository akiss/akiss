(****************************************************************************)
(* Akiss                                                                    *)
(* Copyright (C) 2011-2014 Baelde, Ciobaca, Delaune, Kremer                 *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

let find_in_path x =
  let path = Str.split (Str.regexp ":") (Sys.getenv "PATH") in
  List.find
    Sys.file_exists
    (List.map (fun d -> Filename.concat d x) path)

let maude_binary =
  try
    find_in_path "maude"
  with
    | Not_found ->
        Printf.eprintf "Cound not find maude in PATH!\n" ;
        Printf.eprintf "It is likely that tamarin-prover won't work.\n" ;
        exit 1

let full_maude =
  try
    find_in_path "full-maude.maude"
  with
    | Not_found ->
       Printf.eprintf "Could not find full-maude.maude in PATH!\n";
       exit 1

let maude_command =
  maude_binary ^ " -batch -no-banner -no-ansi-color " ^ full_maude

let tamarin_binary =
  try
    find_in_path "tamarin-prover"
  with
    | Not_found ->
        Printf.eprintf "Cound not find tamarin-prover in PATH!\n" ;
        Printf.eprintf "You may need to add something like \
                        ~/.cabal/bin to it.\n" ;
        exit 1
