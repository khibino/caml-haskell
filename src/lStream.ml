
type 'a t =
    Nil
  | Cons of ('a * (('a t) Lazy.t))

(* Cons (v, (lazy s)) *)

let create_stream init_v to_next last_p =
  let rec next v =
    if last_p v then Cons (v, lazy Nil)
    else Cons (v, (lazy (next (to_next v))))
  in (next init_v)

let is_empty s = (s == Nil)

let peek s =
  match s with
      Nil -> None
    | Cons (car, _) -> Some car

let hd s =
  match s with
      Nil -> failwith "end of stream"
    | Cons (car, _) -> car

let tl s =
  match s with
      Nil -> failwith "end of stream"
    | Cons (_, cdr) -> Lazy.force cdr

let rec fold_left append_fun init s =
  if (is_empty s) then init
  else fold_left append_fun (append_fun init (hd s)) (tl s)

let push_back e s =
  Cons (e, lazy s)

let rec push_back_all stk s =
  match stk with
      [] -> s
    | top :: rest ->
	push_back_all rest (push_back top s)
