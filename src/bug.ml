type a = 
  | No
  | Yes of b  
and b = {
  mutable a : a;
}

let () = 
let foo = { a = No } in
foo.a <- Yes foo ;
Printf.printf "%B%!" (foo = foo)
