
let _ =
  (* try  *)
    Eval.eval_test Sys.argv.(1)
  (* with *)
(*     | e -> Symbol.dump (); raise e *)
