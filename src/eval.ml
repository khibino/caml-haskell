
module L = List
module H = Hashtbl

module OA = OnceAssoc
module T = Token
module LO = Layout
module SYN = Syntax
module PD = SYN.ParsedData
module ID = SYN.Identifier
module D = SYN.Decl
module CA = SYN.Case
module C = SYN.Constructor
module P = SYN.Pattern
module E = SYN.Expression


type 'module_e program_buffer = {
  pdata_assoc : (string, 'module_e PD.t) OA.t;
}

let load_program pdata_list =
  let pa = OA.create
    (fun x -> "Already loaded module: " ^ x)
    (fun k pd -> pd.PD.local_module.PD.mname)
  in
  let _ = L.map (fun pdata -> pa.OA.add pdata.PD.local_module.PD.mname pdata) pdata_list in
    { pdata_assoc = pa; }
      

(* type 'module_e program_buffer = 'module_e PD.t *)

type 'module_e eval_buffer = {
  pat_tbl : (P.pat, 'module_e pre_value ref) H.t;
  pdata : 'module_e program_buffer;
}

and 'module_e env_t = 'module_e eval_buffer list

and 'module_e value =
    Bottom
  | Literal of T.loc SYN.literal
  | Cons of C.con
  | List of 'module_e pre_value list
  | Closure of (P.pat list * E.t * 'module_e env_t) (* function or constructor *)
      (* arguemnt-pattern-list, expression, environment *)

and 'module_e pre_value =
    Thunk of E.t * 'module_e env_t
  | ThunkA of E.aexp * 'module_e env_t
  | Thawed of 'module_e value


let eval_buffer_create pd =
  { pat_tbl = H.create 32; 
    pdata = pd; }

let env_top env = L.hd env

let env_top_symtab env = (env_top env).pat_tbl

(* let new_scope env =
   (eval_buffer_create ()) :: env *)

let env_create pd : 'module_e env_t =
  (eval_buffer_create pd) :: []

let local_env env =
  let top = env_top env in
  let n = H.copy top.pat_tbl in
    { top with pat_tbl = n} :: env

let mk_literal lit =
  Literal lit

let mk_closure env pat_list exp =
  Closure (pat_list, exp, env)

(*
let rec apply_fexp env func_exp aexp_list =
  let closure = eval_func_exp env func_exp in
    apply_closure env closure aexp_list
*)

let rec bind_pat env pat value =
  H.add (env_top_symtab env) (to_pat_for_hash pat) (ref value)

and apply_pat env pat =
  H.find (env_top_symtab env) (to_pat_for_hash pat)

and arity_list_take l n =
  let rec take_rec buf rest nn =
    match (n, rest) with
	(0, _) -> (L.rev buf, rest)
      | (_, f::rest) -> take_rec (f::buf) rest (nn - 1)
      | (_, []) -> failwith
	  (Printf.sprintf "apply_closure: Too many arguemnt(s): expects %d argument(s), but is here applied to %d argument(s)"
	     (L.length l) n)
  in take_rec [] l n

and apply_closure env closure aval_list =
(*   let aval_list = L.map (fun exp -> exp_eval_fun env exp) aexp_list in *)
  match closure with
      Closure (apat_list, body_exp, env (* shadow caller env *)) ->
	let (loc_env, ac) = (local_env env, L.length aval_list) in
	let (pbind_list, apat_rest) = arity_list_take apat_list ac in
	let _  = L.map2 (fun pat v -> bind_pat loc_env pat v) pbind_list aval_list in
	  if apat_rest = [] then eval_exp loc_env body_exp
	  else mk_closure env apat_rest body_exp
	      
    | x -> failwith (Printf.sprintf "apply_closure: Not closure value: %s" (Std.dump x))

and eval_atom_exp env aexp = fst (eval_atom_exp_switch env aexp)

and eval_arg_atom_exp env aexp = snd (eval_atom_exp_switch env aexp)

and eval_atom_exp_switch env =
  function
      E.VarE (id) as atom_exp ->
	((let varref = apply_pat env (P.VarP id) in
	    match !varref with
		Thunk (e, tenv) ->
		  let v = eval_exp tenv e in
		    varref := Thawed v;
		    v
	      |	ThunkA (ae, tenv) ->
		  let v = eval_atom_exp tenv ae in
		    varref := Thawed v;
		    v
	      | Thawed v -> v),

	 ThunkA (atom_exp, env))
		 
	 
    | E.LiteralE (lit) -> let l = Literal lit in (l, Thawed l)

    | E.ParenE (exp) -> eval_exp_switch env exp

    | E.ListE (el) as atom_exp -> (List (L.map (fun e -> eval_arg_exp env e) el), ThunkA (atom_exp, env))

    | x -> failwith (Printf.sprintf "exp: Not implemented:\n%s" (Std.dump x))

and eval_func_exp env =
  function
      E.FfunE aexp ->
	eval_atom_exp env aexp

    | E.FappE (fexp, aexp) -> 
	apply_closure env (eval_func_exp env fexp) (L.map (fun e -> eval_arg_atom_exp env e) [aexp])

    | E.FappEID -> failwith ("BUG: E.FappEID found.")

and eval_exp env exp = fst (eval_exp_switch env exp)

and eval_arg_exp env exp = snd (eval_exp_switch env exp)

and eval_exp_switch env =
  function
      E.Top (E.LambdaE (apat_list, exp), None) ->
	let c = mk_closure env apat_list exp in
	  (c, Thawed c)
    | E.Top (E.FexpE (E.FfunE (E.LiteralE lit)), None) ->
	let l = mk_literal lit in
	  (l, Thawed l)
    | nv_exp ->
	((match nv_exp with
	    | E.Top (E.FexpE fexp, None) -> eval_func_exp env fexp

	    | E.Top (E.VarOp2E (op, lexp, rexp), None) ->
		apply_closure env (eval_atom_exp env (E.VarE op)) (L.map (fun e -> eval_arg_exp env e) [lexp; rexp])

	    | E.Top (E.LetE (decl_list, exp), None) -> 
		let loc_env = local_env env in
		let _ = L.map (fun decl -> eval_decl loc_env decl) decl_list in
		  eval_exp loc_env exp
	    | E.Top (E.IfE (pre_e, then_e, else_e), None) -> 
		(match (eval_exp env pre_e) with
		     Cons(C.App (id, _)) when id.ID.name = "True" -> eval_exp env then_e
		   | Cons(C.App (id, _)) when id.ID.name = "False" -> eval_exp env else_e
		   | _  -> Bottom)
	    | E.Top (E.CaseE (exp, []), None) ->
		Bottom
	    | E.Top (E.CaseE (exp, (CA.Simple (pat, case_exp, [])) :: alt_list), None) ->
		let loc_env = local_env env in
		let _ = bind_pat loc_env pat (Thunk (exp, loc_env)) in
		  if match_p pat env exp then
		    eval_exp loc_env case_exp
		  else
		    eval_exp env (E.Top (E.CaseE (exp, alt_list), None))

	    | x -> failwith (Printf.sprintf "exp: Not implemented:\n%s" (Std.dump x))),

	 Thunk (nv_exp, env))

and pre_eval_rhs env =
  function
      D.Rhs (exp, None) ->
	((fun funlhs ->
	    let _ = match funlhs with
		D.FunDecLV (sym, apat_list) ->
		  bind_pat env (P.VarP sym) (Thawed (mk_closure env apat_list exp))
	      | D.Op2Pat (op, (arg1, arg2)) ->
		  bind_pat env (P.VarP op) (Thawed (mk_closure env [arg1; arg2] exp))
	      | x -> failwith (Printf.sprintf "rhs1: Not implemented:\n%s" (Std.dump x))
	    in ()),
	 (fun pat ->
	    bind_pat env pat (Thunk (exp, env));
(* 	    match_p env pat exp; *)
	    ()))
(*     | D.Rhs (exp, Some exp_decl_list) -> *)
    | x ->
	failwith (Printf.sprintf "rhs0: Not implemented:\n%s" (Std.dump x))

and eval_decl env =
  function
      D.FunDec (lhs, (D.Rhs (exp, None) as rhs)) ->
	let (bf, _) = pre_eval_rhs env rhs in
	  bf lhs
    | D.PatFunDec (pat, (D.Rhs (exp, None) as rhs)) ->
	let (_, bp) = pre_eval_rhs env rhs in
	  bp pat
    | x -> failwith (Printf.sprintf "decl: Not implemented:\n%s" (Std.dump x))

and eval_topdecl env =
  function 
      D.Decl d -> eval_decl env d
    | x -> failwith (Printf.sprintf "topdecl: Not implemented:\n%s" (Std.dump x))

and eval_module env =
  function
(*       (x, y, (z, topdecl_list)) -> (x, y, (z, List.map (eval_topdecl env) topdecl_list)) *)
      (x, y, (z, topdecl_list)) ->
	let _ = List.map (eval_topdecl env) topdecl_list in ()

and eval_program env program =
  let _ = program.pdata_assoc.OA.iter (fun name pd -> eval_module env pd.PD.syntax) in
  let main_pd = program.pdata_assoc.OA.find "Main" in
    eval_atom_exp env (E.VarE (ID.make_id_core "main" (ID.Qual main_pd.PD.local_module.PD.mn_ref) T.implicit_loc))


(* Scan Pattern *)
and scan_pattern p =
  match p with
      P.PlusP (id, i64, _) ->
	(P.PlusP ((ID.unloc id), i64, T.implicit_loc),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))
    | P.VarP (id) ->
	(P.VarP (ID.unloc id),
	 (fun env exp ->
	    let _ = bind_pat env (P.VarP (id)) (Thawed (eval_exp env exp)) in
	      true
	 ))
    | P.AsP (id, pat) ->
	(P.AsP (ID.unloc id, to_pat_for_hash pat),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))
    | P.ConP (id, pat_list) ->
	(P.ConP (ID.unloc id, L.map to_pat_for_hash pat_list),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))
    | P.LabelP (id, fpat_list) ->
	(P.LabelP (ID.unloc id, L.map (fun (id, pat) -> (ID.unloc id, pat)) fpat_list),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))
    | P.LiteralP literal ->
	(P.LiteralP (SYN.unloc_literal literal),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))
    | P.WCardP ->
	(P.WCardP,
	 (fun _ _ -> true))
    | P.TupleP pat_list ->
	(P.TupleP (L.map to_pat_for_hash pat_list),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))
    | P.ListP pat_list ->
	(P.ListP (L.map to_pat_for_hash pat_list),
	 (fun env exp ->
	    let v = eval_exp env exp in
	      match v with
		  List pre_vl ->
		    let _ = L.map2 (fun pat pre_v -> bind_pat env pat pre_v) pat_list pre_vl in
		       true
		| _ -> false
	 ))
    | P.MIntP (int64, _) ->
	(P.MIntP (int64, T.implicit_loc),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))
    | P.MFloatP (float, _) ->
	(P.MFloatP (float, T.implicit_loc),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))
    | P.Irref pat ->
	(P.Irref (to_pat_for_hash pat),
	 (fun env exp ->
	    bind_pat env pat (Thunk (exp, env));
	    true))

    (*     | P.Pat0 of pat op2list_patf *)
    (*     | P.Pat1 of pat op2list_patf *)

    | P.ConOp2P (id, pat1, pat2) ->
	(P.ConOp2P (ID.unloc id, (to_pat_for_hash pat1), (to_pat_for_hash pat2)),
	 (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p))))

    | _ -> failwith ("Not converted Pat0 or Pat1 found. parser BUG!!")

and to_pat_for_hash p = fst (scan_pattern p)
and match_p p = snd (scan_pattern p)

(* 
let eval_test fn =
  let pdata = LO.parse_test fn in
    eval_module pdata (env_create ()) pdata.PD.syntax
*)

