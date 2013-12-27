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

open Term

let () =
  fsymbols := [
    ("enc",2); ("dec",2);
    ("pair",2); ("fst",1); ("snd",1);
    ("a",0)
  ]

let dec x y = Fun("dec",[x;y])
let enc x y = Fun("enc",[x;y])
let pair x y = Fun("pair",[x;y])
let fst p = Fun("fst",[p])
let snd p = Fun("snd",[p])
let a = Fun("a",[])

let rules = [ dec (enc (Var "X") (Var "XX")) (Var "XX"), Var "X" ;
              fst (pair (Var "X") (Var "XX")), Var "X" ;
              snd (pair (Var "X") (Var "XX")), Var "XX" ]

let () =
  let substs = Tamarin.unifiers (dec (Var "X") a) (Var "XX") rules in
    List.iter (fun s -> Printf.printf "> %s\n" (show_subst s)) substs
