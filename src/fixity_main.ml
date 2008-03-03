
module SYN = Syntax
(* module PBuf = SYN.ParseBuffer *)
module PD = SYN.ParsedData
(* module D = SYN.Decl *)
module LO = Layout

let _ =
  let _ = (print_endline "fixity check mode\n---",
	   (LO.debugFlag := true),
	   (LO.debugFlagFixity := false)) in
  let pd = LO.parse_with_prelude (Util.unix_input_chan ()) in
  let _ = print_endline "--- data dump ---" in
    PD.dump_module pd.PD.local_module

(* For interactive memo *)
(* let pd = SYN.go_prelude_mode ()  *)
