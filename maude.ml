
open Term

let debug = true
let pdebug = false (* show parsing info *)
let sdebug = pdebug || false (* show maude script *)

let output_string = Cime.output_string

let input_line chan =
  let line = input_line chan in
    if pdebug then
      Format.printf "input line > %S\n%!" line ;
    line

(** Printing Maude terms and modules *)

let rec print chan = function

  | Fun ("!tuple!",l) ->
      let n = List.length l in
      let f = Format.sprintf "akiss%duple" n in
        print chan (Fun (f,l))
  | Fun ("!test!",[]) ->
      print chan (Fun ("akisstest",[]))
  | Fun ("!out!",s) ->
      print chan (Fun ("akissout",s))
  | Fun ("!in!",s) ->
      print chan (Fun ("akissin",s))

  | Fun ("A",[]) -> output_string chan "akisschA"
  | Fun ("B",[]) -> output_string chan "akisschB"
  | Fun ("C",[]) -> output_string chan "akisschC"

  | Fun (s,[]) | Var s ->
      begin try
        Scanf.sscanf s "w%d"
          (fun _ -> Format.fprintf chan "akissw%s" s)
      with Scanf.Scan_failure _ ->
        begin try
          Scanf.sscanf s "!n!%d"
            (fun n -> Format.fprintf chan "akissn%d" n)
        with Scanf.Scan_failure _ ->
          output_string chan s
        end
      end
  | Fun (s,args) ->
      Format.fprintf chan "%s(%a)" s (Cime.pp_list print ", ") args

let sprint t =
  print Format.str_formatter t ;
  Format.flush_str_formatter ()

let rec times n f =
  if n = 0 then () else begin f () ; times (n-1) f end

let cursig = ref []

let print_module rules extrasig chan () =
  cursig := [] ;
  let op name arity =
    cursig := (name,arity) :: !cursig ;
    Format.fprintf chan "op %s : %a-> Term .\n" name
      (fun chan () -> times arity (fun () -> Format.fprintf chan "Term "))
      ()
  in
    Format.fprintf chan "(mod AKISS is\nsorts Term .\n" ;

    (* Constructors for tuples, actions, worlds and predicates *)
    op "akiss0uple" 0 ; op "akiss1uple" 1 ; op "akiss2uple" 2 ;
    op "akissout" 1 ; op "akissin" 2 ; op "akisstest" 0 ;
    op "world" 2 ; op "empty" 0 ;
    op "knows" 3 ; op "reach" 1 ; op "identical" 3 ; op "ridentical" 3 ;
    (* TODO same as cime: don't hardcode *)
    op "akisschA" 0 ;
    op "akisschB" 0 ;
    op "akisschC" 0 ;

    (* Declarations from the input file: theory symbols and private names *)
    List.iter
      (fun (f,n) ->
         if f = "plus" then
           Format.fprintf chan "op plus : Term Term -> Term [assoc comm] .\n"
         else
           op f n)
      !fsymbols ;
    List.iter (fun v -> op v 0) !private_names ;

    (* Parameters, names and variables not declared in input file
     * but present in the term, given as extrasig. *)
    List.iter
      (fun n -> op ("akissw" ^ string_of_int n) 0)
      extrasig.params ;
    List.iter
      (fun n -> op ("akissn" ^ string_of_int n) 0)
      extrasig.names ;
    if !vars <> [] || extrasig.vars <> [] then
      Format.fprintf chan "var %a : Term .\n"
        (Cime.pp_list output_string " ")
        (List.rev_append !vars extrasig.vars) ;

    (* Rewrite rules *)
    let c = ref 0 in
    List.iter
      (fun (left,right) ->
         incr c ;
         Format.fprintf chan
           "eq [rule%d] : %a = %a [variant] .\n"
           !c print left print right)
      rules ;

    Format.fprintf chan "endm)\n\n"

(** Interacting with a full-maude process *)

let chan_out,chan_in =
  let o,i =
    let home = Sys.getenv "HOME" in
    Unix.open_process
      (home ^ "/soft/maude/maude -batch -no-banner -no-ansi-color " ^
       home ^ "/soft/maude/full-maude.maude")
  in
    at_exit (fun () -> ignore (Unix.close_process (o,i))) ;
    o,
    (Format.formatter_of_out_channel i)

let run_maude print_command parse_result =
  if sdebug then print_command Format.std_formatter ;
  Format.print_flush () ;
  print_command chan_in ;
  Format.pp_print_flush chan_in () ;
  parse_result chan_out

(** Parsing results *)

let tokens chan =
  let stream = Stream.of_channel chan in
  let keywords =
    [ ":";";";",";"{";"}";"(";")";"-->" ]
  in
    Genlex.make_lexer keywords stream

let is_var s =
  s.[0] = '#' ||
  s.[0] = 'X' ||
  List.mem s !vars

let arity f =
  if is_var f then 0 else
    List.assoc f !cursig

let parse_var tokens =
  match Stream.next tokens with
    | Genlex.Ident "#" ->
        begin match Stream.next tokens with
          | Genlex.Int i -> "#" ^ string_of_int i
          | _ -> assert false
        end
    | Genlex.Ident s -> s
    | _ -> assert false

let string_of_token = function
  | (Genlex.Kwd k) -> "K("^k^")"
  | (Genlex.Ident k) -> "I("^k^")"
  | _ -> "?"

let string_of_peek t =
  match Stream.peek t with
    | None -> "$"
    | Some t -> string_of_token t

(** Translating symbol names back to Akiss conventions *)
let translate_symbol = function
  | "akisstest" -> "!test!"
  | "akissout" -> "!out!"
  | "akissin" -> "!in!"
  | "akiss0uple" | "akiss_1uple" | "akiss_2uple" -> "!tuple!"
  | "akisschA" -> "A"
  | "akisschB" -> "B"
  | "akisschC" -> "C"
  | s when Util.startswith ~prefix:"akiss" s ->
      begin try
        Scanf.sscanf s "akissw%d" (fun d -> "w" ^ string_of_int d)
      with _ ->
        Scanf.sscanf s "akissn%d" (fun d -> "!n!" ^ string_of_int d)
      end
  | s -> s

exception Parse_error

let expect tokens x =
  if pdebug then Format.printf "Expecting %s...\n%!" (string_of_token x) ;
  let t = Stream.next tokens in
    if x <> t then begin
      Format.printf
        "Parse error: expected %s, got %s!\n%!"
        (string_of_token x) (string_of_token t) ;
      raise Parse_error
    end

let rec parse_term tokens =
  let expect = expect tokens in
  if pdebug then Format.printf "pt> %s\n" (string_of_peek tokens) ;
  match Stream.next tokens with
    | Genlex.Ident "#" ->
        begin match Stream.next tokens with
          | Genlex.Int i ->
              if pdebug then Format.printf "pt> #%d\n%!" i ;
              expect (Genlex.Kwd ":") ;
              expect (Genlex.Ident "Term") ;
              Var ("#" ^ string_of_int i)
          | _ -> assert false
        end
    | Genlex.Ident "plus" ->
        expect (Genlex.Kwd ("(")) ;
        let l = parse_list tokens in
          expect (Genlex.Kwd (")")) ;
          List.fold_left
            (fun a b -> Fun ("plus",[a;b]))
            (List.hd l) (List.tl l)
    | Genlex.Ident s ->
        if is_var s then begin
          expect (Genlex.Kwd ":") ;
          expect (Genlex.Ident "Term") ;
          Var s
        end else begin
          if pdebug then Format.printf "pt> arity(%s) = %!" s ;
          let a = arity s in
          let s = translate_symbol s in
          if pdebug then Format.printf "%d\n%!" a ;
          if a = 0 then Fun (s,[]) else begin
            expect (Genlex.Kwd "(") ;
            let l = parse_terms a tokens in
              expect (Genlex.Kwd ")") ;
              Fun (s,l)
          end
        end
    | _ -> failwith "not a term"
and parse_terms n tokens =
  if n = 0 then [] else
    let t = parse_term tokens in
    if n > 1 then expect tokens (Genlex.Kwd ",") ;
    let l = parse_terms (n-1) tokens in
      t :: l
and parse_list tokens =
  let t = parse_term tokens in
    if Stream.peek tokens <> Some (Genlex.Kwd ",") then [t] else begin
      Stream.junk tokens ;
      t :: parse_list tokens
    end

let rec parse_substitution tokens =
  if Stream.peek tokens = Some (Genlex.Ident "empty") then begin
    expect tokens (Genlex.Ident "empty") ;
    expect tokens (Genlex.Ident "substitution") ;
    []
  end else
    let x = parse_var tokens in
      if pdebug then Format.printf "ps> var %s\n%!" x ;
      expect tokens (Genlex.Kwd ":") ;
      expect tokens (Genlex.Ident "Term") ;
      expect tokens (Genlex.Kwd "-->") ;
      let t = parse_term tokens in
        match Stream.peek tokens with
          | Some (Genlex.Kwd ";") ->
              Stream.junk tokens ;
              (x,t) :: parse_substitution tokens
          | _ -> [x,t]

let parse_variant tokens =
  let expect = expect tokens in
  expect (Genlex.Kwd "{") ;
  let t = parse_term tokens in
    expect (Genlex.Kwd ",") ;
    let s = parse_substitution tokens in
      expect (Genlex.Kwd "}") ;
      t,s

let rec parse_variants tokens =
  match Stream.peek tokens with
    | Some (Genlex.Kwd "{") ->
        let v = parse_variant tokens in
        let vs = parse_variants tokens in
          v :: vs
    | Some (Genlex.Ident "No") ->
        expect tokens (Genlex.Ident "No") ;
        expect tokens (Genlex.Ident "more") ;
        expect tokens (Genlex.Ident "variants") ;
        []
    | Some t ->
        if pdebug then Format.printf "pvs> skip %s\n%!" (string_of_token t) ;
        Stream.junk tokens ;
        parse_variants tokens
    | None -> assert false

let rec parse_unifiers tokens =
  match Stream.peek tokens with
    | Some (Genlex.Ident "Solution") ->
        Stream.junk tokens ; (* Solution *)
        Stream.junk tokens ; (* <int> *)
        let s = parse_substitution tokens in
          s :: parse_unifiers tokens
    | Some (Genlex.Ident "No") ->
        expect tokens (Genlex.Ident "No") ;
        expect tokens (Genlex.Ident "more") ;
        expect tokens (Genlex.Ident "solutions") ;
        []
    | Some t ->
        if pdebug then Format.printf "pvs> skip %s\n%!" (string_of_token t) ;
        Stream.junk tokens ;
        parse_unifiers tokens
    | None -> assert false

(** Putting everything together *)

let variants t rules =
  let esig = sig_of_term_list [t] in
    run_maude
      (fun chan ->
         Format.fprintf chan "%a\n" (print_module rules esig) () ;
         Format.fprintf chan "(get variants %a .)\n" print t)
      (fun chan ->
         while
           not (Util.startswith ~prefix:"get variants" (input_line chan))
         do () done ;
         parse_variants (tokens chan))

let variants t rules =
  let v = variants t rules in
    if debug then begin
      Format.printf "variants %s (%d solutions):\n"
        (show_term t) (List.length v) ;
      List.iter
        (fun (t,s) ->
           Format.printf " %s, %s\n" (show_term t) (show_subst s))
        v
    end ;
    v

let unifiers s t rules =
  let esig = sig_of_term_list [s;t] in
    run_maude
      (fun chan ->
         Format.fprintf chan "%a\n" (print_module rules esig) () ;
         Format.fprintf chan "(unify %a =? %a .)\n" print s print t)
      (fun chan ->
         while not (Util.startswith ~prefix:"unify in " (input_line chan))
         do () done ;
         parse_unifiers (tokens chan))

let unifiers s t rules =
  let v = unifiers s t rules in
    if debug then begin
      Format.printf "unifiers %s %s (%d solutions):\n%!"
        (show_term s) (show_term t) (List.length v) ;
      List.iter (fun s -> Format.printf " %s\n" (show_subst s)) v
    end ;
    v

let equals s t rules =
  if s = t then true else
  let esig = sig_of_term_list [s;t] in
    run_maude
      (fun chan ->
         Format.fprintf chan "%a\n" (print_module rules esig) () ;
         Format.fprintf chan "(red %a == %a .)\n" print s print t)
      (fun chan ->
         while input_line chan <> "result Bool :" do () done ;
         input_line chan = "  true")

let equals s t rules =
  let b = equals s t rules in
    if debug then
      Format.printf "equals %s %s: %b\n"
        (show_term s) (show_term t) b ;
    b