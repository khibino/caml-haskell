
let parse_error_flag = ref false

let is_error () = !parse_error_flag

let clear_error () =
  parse_error_flag := false

