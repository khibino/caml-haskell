
module H = Hashtbl

type ('a, 'b) t = {
  (*     t : ('a, b) H.t; *)
  (*     dup_err : string -> string; *)
  mem : ('a -> bool);
  find : ('a -> 'b);
  add : ('a -> 'b -> unit);
  replace : ('a -> 'b -> unit);

  iter : (('a -> 'b -> unit) -> unit);
  to_string : (unit -> string);
}

let create_symtab () = Hashtbl.create 32

let debug = false
let assocId = ref 0

let create err_fun to_str_fun = 
  let tbl = create_symtab () in 
  let id = !assocId in 
  let _ = (assocId := id + 1) in {
      mem = (fun k -> H.mem tbl k);
      find = (fun k ->
		if debug then Printf.printf "find called with %s against assoc %d\n" k id;
		H.find tbl k);
      add = (fun k v ->
	       if debug then Printf.printf "add called with %s against assoc %d\n" k id;
	       if H.mem tbl k then failwith (err_fun k)
	       else H.add tbl k v);
      replace = (fun k v -> 
		   if debug then Printf.printf "replace called with %s against assoc %d\n" k id;
		   H.replace tbl k v);

      iter = (fun f -> H.iter f tbl);
      to_string = (fun () -> H.fold (fun k v c -> c ^ (to_str_fun k v) ^ "\n") tbl "");
    }