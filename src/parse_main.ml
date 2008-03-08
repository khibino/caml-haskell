
module SYN = Syntax
module PB = SYN.ParseBuffer
module LO = Layout

let _ =
  let _ = (output_string stderr "parse0 mode\n===", (LO.debugFlag := true)) in
  let pb = PB.create () in
  let _ = assert (pb == PB.last_buffer ()) in
  let _ = LO.parse0_chan (Util.unix_input_chan ()) in ()
