
module LO = Layout

let _  =
  let _ = (output_string stderr "layout output\n===", (LO.debugFlag := true)) in
    LO.dump_tok_stream
      (LO.layout
	 (LO.create_input
	    (LO.all_token_rev_list
	       (Lexing.from_channel (Util.unix_input_chan ())))) [])
