(* それぞれのkeyに対するvalueを一度だけ代入できる Hashtbl *)

module H = Hashtbl

module F = Printf

type ('a, 'b) t = {
  tbl : ('a, 'b) H.t;
  dup_err : string -> string;
  string_of_entry : 'a -> 'b -> string;

  mem : ('a -> bool);
  find : ('a -> 'b);
  add : ('a -> 'b -> unit);
  replace : ('a -> 'b -> unit);

  iter : (('a -> 'b -> unit) -> unit);
  to_string : (unit -> string);
}

let create_symtab () = Hashtbl.create 32

let debug = false
let nextAssocId = ref 0

let create err_fun to_str_fun = 
  let tbl = create_symtab () in 
  let id = !nextAssocId in 
  let _ = (nextAssocId := id + 1) in {
      tbl = tbl;
      dup_err = err_fun;
      string_of_entry = to_str_fun;

      mem = (fun k -> H.mem tbl k);
      find = (fun k ->
		if debug then F.printf "find called with %s against assoc %d\n" k id;
		H.find tbl k);
      add = (fun k v ->
	       if debug then F.printf "add called with %s against assoc %d\n" k id;
	       if H.mem tbl k then failwith (err_fun k)
	       else H.add tbl k v);
      replace = (fun k v -> 
		   if debug then F.printf "replace called with %s against assoc %d\n" k id;
		   H.replace tbl k v);

      iter = (fun f -> H.iter f tbl);
      to_string = (fun () -> H.fold (fun k v c -> c ^ (to_str_fun k v) ^ "\n") tbl "");
    }

let tie_hashtbl hfun store k =
  hfun store.tbl k

let mem store k =
  tie_hashtbl H.mem store k

let find store k =
  tie_hashtbl H.find store k


let add store k v =
  if H.mem store.tbl k then
    failwith (store.dup_err k)
  else H.add store.tbl k v

let iter f store =
  H.iter f store.tbl

let to_string store =
  H.fold (fun k v c -> c ^ (store.string_of_entry k v) ^ "\n") store.tbl ""
