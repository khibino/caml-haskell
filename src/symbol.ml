(* シンボルテーブル *)

module S = String
module H = Hashtbl

type t
type table = (string, t) H.t

external of_string: string -> t = "%identity"
external name     : t -> string = "%identity"

let create_table () : table = Hashtbl.create 32

let intern_to tbl name =
  if H.mem tbl name then H.find tbl name
  else
    let newsym = of_string (S.copy name) in
    let () = H.add tbl name newsym in
      newsym

let globalTable = create_table ()

let intern name = intern_to globalTable name
