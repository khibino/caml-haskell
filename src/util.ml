
(* テスト用ファイル入力 *)
let unix_input_chan () =
  if Array.length Sys.argv < 2 then stdin
  else (open_in_bin Sys.argv.(1))
