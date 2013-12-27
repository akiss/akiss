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
