
module F = Printf
module H = Hashtbl

module S = Symbol
module SYN = Syntax
module SAH = SaHashtbl
module LO = Layout
module E = Eval

let _ =
  let _ = (output_string stderr "--- fixity check mode ---\n",
	   (* (LO.debugFlag := true) *)
           (LO.debugFlag := false)
          ) in
  let (ex, prog) =
    E.fixity_eval_program
      (E.load_program
         (LO.parse_with_prelude
            (Util.unix_input_chan ()))) in
  let _ = output_string stderr "--- data dump ---\n" in
    SaHt.fold
      (fun name modbuf () ->
         H.fold
           (fun opsym (fixity, _) () ->
              F.fprintf stderr "%s: %s: %s\n"
                (S.name name)
                (S.name opsym)
                (SYN.fixity_str fixity))
           (E.module_fixity modbuf)
           ())
      prog
      ()
