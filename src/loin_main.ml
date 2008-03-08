
module LO = Layout

let _ =
  let _ = (output_string stderr "layout input\n===", (LO.debugFlag := true)) in
    LO.dump_tok_stream
      (LO.create_input
	 (LO.all_token_rev_list
	    (Lexing.from_channel stdin)))
