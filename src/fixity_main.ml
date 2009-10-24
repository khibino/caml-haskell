
module SYN = Syntax
module PBuf = SYN.ParseBuffer
module SAH = SaHashtbl
module PD = SYN.ParsedData
(* module D = SYN.Decl *)
module LO = Layout

let _ =
  let _ = (output_string stderr "--- fixity check mode ---\n",
	   (LO.debugFlag := true),
	   (LO.debugFlagFixity := false),
	   (PD.debugFlag := true)) in
  let pd = LO.parse_with_prelude (Util.unix_input_chan ()) in
  let _ = output_string stderr "--- data dump ---\n" in
    output_string stderr (SAH.to_string pd.PD.module_assoc)
