(*  *)

type ('a, 'b) t = {
  mutable rev_order : 'a list;
  map : ('a, 'b) Hashtbl.t;
}

let create size =
  { rev_order = []; map = Hashtbl.create size }

let add tbl key value =
  let _ = ((tbl.rev_order <- (key :: tbl.rev_order)),
           Hashtbl.add tbl.map key value)
  in tbl

let replace tbl key value =
  let _ = (if not (Hashtbl.mem tbl.map key) then
             tbl.rev_order <- (key :: tbl.rev_order))
  in
    Hashtbl.replace tbl.map key value

let of_list pairs =
  let rec of_list pairs oh =
      match pairs with
          [] -> oh
        | (k, v) :: rest -> of_list rest (add oh k v)
  in of_list pairs (create (List.length pairs))

let ro_op hash_fun tbl key = hash_fun tbl.map key

let find tbl key =
  let hash_fun = Hashtbl.find in
    ro_op hash_fun tbl key

let mem tbl key = 
  let hash_fun = Hashtbl.mem in
    ro_op hash_fun tbl key

let order_map func tbl order =
  List.rev (List.rev_map (fun key ->
                            func key (find tbl key)) order)

let rev_map func tbl =
  order_map func tbl tbl.rev_order

let map func tbl =
  order_map func tbl (List.rev tbl.rev_order)

let key_list tbl =
  List.rev tbl.rev_order

let value_list tbl =
  List.rev_map (fun key -> find tbl key) tbl.rev_order
