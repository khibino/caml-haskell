
module SYN = Syntax
module PB = SYN.ParseBuffer
module LO = Layout

let _ =
  let _ = (print_endline "parse0 mode\n===", (LO.debugFlag := true)) in
  let _ =
    if Array.length Sys.argv > 2 then SYN.go_prelude_mode ()
    else PB.create () in
  let _ =  LO.parse0_chan (Util.unix_input_chan ()) in ()
