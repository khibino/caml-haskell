(* それぞれのkeyに対するvalueを一度だけ代入できる Hashtbl *)

module H = Hashtbl

module F = Printf

type ('a, 'b) t = {
  tbl : ('a, 'b) H.t;
  id : int;
  dup_err : string -> string;
  string_of_entry : 'a -> 'b -> string;
}

let create_symtab () = Hashtbl.create 32

let debug = false
let nextAssocId = ref 0

let create err_fun to_str_fun = 
  let id = !nextAssocId in 
  let _ = (nextAssocId := id + 1) in
  let tbl = create_symtab () in {
      tbl = tbl;
      id = id;
      dup_err = err_fun;
      string_of_entry = to_str_fun;
    }

let debug_fun =
  if debug then
    (fun n k id -> F.printf "%s called with %s against assoc %d\n" n k id)
  else
    (fun _ _ _ -> ())

let keyarg_hashtbl hfun store k =
  hfun store.tbl k

let mem store k =
  keyarg_hashtbl H.mem store k

let find store k =
  debug_fun "find" k store.id;
  keyarg_hashtbl H.find store k


let add store k v =
  debug_fun "add" k store.id;
  if H.mem store.tbl k then
    failwith (store.dup_err k)
  else H.add store.tbl k v

let replace store k v =
  debug_fun "replace" k store.id;
  H.replace store.tbl k v

let iter f store =
  H.iter f store.tbl

let to_string store =
  H.fold (fun k v c -> c ^ (store.string_of_entry k v) ^ "\n") store.tbl ""
