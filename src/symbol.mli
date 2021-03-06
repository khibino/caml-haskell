type t
type table

(* val create_table  : unit -> table *)
(* val intern_to   : table -> string -> t *)

val name  : t -> string
val intern: string -> t

val print: Format.formatter -> t -> unit

val dump: unit -> unit
