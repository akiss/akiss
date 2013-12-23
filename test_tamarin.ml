
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
