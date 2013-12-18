(** We use Tamarin (branch feature-ac-rewrite-rules) to compute
  * variants modulo AC because the feature is broken in Maude. *)

open Term

let debug = false
let pdebug = false (* show parsing info *)
let sdebug = pdebug || false (* show script *)

let output_string ch s = Format.fprintf ch "%s" s

let input_line chan =
  let line = input_line chan in
    if pdebug then
      Format.printf "input line > %S\n%!" line ;
    line

let rec pp_list pp sep chan = function
  | [] -> ()
  | [x] -> pp chan x
  | x::tl ->
      pp chan x ;
      output_string chan sep ;
      pp_list pp sep chan tl

(** Printing *)
let rec print chan = function
  | Fun ("plus",[a;b]) ->
      Format.fprintf chan "(%a+%a)" print a print b

  | Fun ("!test!",[]) ->
      Format.fprintf chan "akisstest"
  | Fun ("!out!",[Fun(c,[])]) ->
      Format.fprintf chan "akissout('%s')" c
  | Fun ("!in!",[Fun(c,[]);t]) ->
      Format.fprintf chan "akissin('%s',%a)" c print t

  | Fun (s,[]) when List.mem s !private_names ->
      Format.fprintf chan "'%s'" s

  | Fun (s,[]) | Var s ->
      begin try
        Scanf.sscanf s "w%d"
          (fun _ -> assert false)
      with Scanf.Scan_failure _ ->
        begin try
          Scanf.sscanf s "!n!%d"
            (fun n -> assert false)
        with Scanf.Scan_failure _ ->
          output_string chan s
        end
      end

  | Fun (s,args) ->
      Format.fprintf chan "%s(%a)" s (pp_list print ", ") args

(** Parse variants *)

(** Running and interacting with tamarin-prover *)
let process print_query parse_result =
  let chan_out,chan_in =
    Unix.open_process (Config.tamarin_binary ^ " variants")
  in
  let chan_in = Format.formatter_of_out_channel chan_in in
    if sdebug then print_query Format.std_formatter ;
    Format.print_flush () ;
    print_query chan_in ;
    Format.pp_print_flush chan_in () ;
    parse_result chan_out

let variants t rules =
  if debug then
    Format.printf "<< tamarin variants: %s\n" (show_term t) ;
  let query chan =
    Format.fprintf chan
      "functions: akisstest/0, akissin/2, akissout/1\n" ;
    Format.fprintf chan
      "functions: world/2, empty/0\n" ;
    (* Term signature *)
    List.iter
      (fun (f,n) ->
         if f <> "plus" then
           Format.fprintf chan "functions: %s/%d\n" f n)
      !fsymbols ;
    (* Rewrite rules *)
    List.iter
      (fun (left,right) ->
         Format.fprintf chan "equations: %a = %a\n" print left print right)
      rules ;
    Format.fprintf chan ".\n" ;
    Format.fprintf chan "variants %a\n" print t ;
    Format.fprintf chan ".\n"
  in
  let parse_variants ch =
    match Parsetam.main Lextam.token (Lexing.from_channel ch) with
      | [`Variants substs] ->
          if debug then
            List.iter
              (fun s -> Printf.printf "result> %s\n" (show_subst s))
              substs ;
          let norm x = Maude.normalize x rules in
          let result =
            List.map (fun s -> norm (apply_subst t s), s) substs
          in
            if debug then
              List.iter
                (fun (t,s) ->
                   Printf.printf
                     "Result> %s,%s\n" (show_term t) (show_subst s))
                result ;
            result
      | _ -> assert false
  in
  let parse_variants ch =
    try parse_variants ch with
      | Parsing.Parse_error as e ->
          Format.printf
            "Error while parsing tamarin-prover output.\n" ;
          query Format.std_formatter ;
          raise e
  in
    process query parse_variants
