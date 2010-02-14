(* それぞれのkeyに対するvalueを一度だけ代入できる Hashtbl *)

module H = Hashtbl

module F = Printf

type ('a, 'b) t = {
  tbl : ('a, 'b) H.t;
  key_str : 'a -> string;
  val_str : 'b -> string;

  dup_err_fmt : string -> string;
  entry_fmt : string -> string -> string;

  name : string;
}

let create_symtab () = Hashtbl.create 32

let debug = false

let create key_str val_str dfmt efmt name = 
  let tbl = create_symtab () in {
      tbl = tbl;
      key_str = key_str;
      val_str = val_str;

      dup_err_fmt = dfmt;
      entry_fmt = efmt;

      name = name;
    }
  
let debug_fun =
  if debug then
    (fun n k name -> F.printf "%s called with %s against assoc %s\n" n k name)
  else
    (fun _ _ _ -> ())


let keyarg_hashtbl hfun store k =
  hfun store.tbl k

let mem store k =
  keyarg_hashtbl H.mem store k

let find store k =
  debug_fun "find" (store.key_str k) store.name;
  keyarg_hashtbl H.find store k

let add store k v =
  debug_fun "add" (store.key_str k) store.name;
  if H.mem store.tbl k then
    failwith (store.dup_err_fmt (store.key_str k))
  else H.add store.tbl k v

let replace store k v =
  debug_fun "replace" (store.key_str k) store.name;
  H.replace store.tbl k v

let iter f store =
  H.iter f store.tbl

let fold f store iv =
  H.fold f store.tbl iv

let to_string store =
  H.fold (fun k v c -> c ^ (store.entry_fmt (store.key_str k) (store.val_str v)) ^ "\n") store.tbl ""
