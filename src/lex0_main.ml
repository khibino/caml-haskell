module L0 = Lexer0
module P = Parser

let _ =
  let lexbuf = Lexing.from_channel (Util.unix_input_chan ()) in
  let rec dump_all () =
    let tok = (L0.token lexbuf) in
    let _ = print_endline (L0.to_string_with_loc tok) in
      match tok with
	  P.EOF _ -> ()
	| _ -> dump_all ()
  in
  let _ = print_endline "lexer output\n===" in
    dump_all ()
