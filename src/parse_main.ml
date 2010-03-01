
module SYN = Syntax
module LO = Layout

let _ =
  let _ = (output_string stderr "parse0 mode\n===", (LO.debugFlag := true)) in
  let _ = LO.parse0_chan (Util.unix_input_chan ()) in ()
