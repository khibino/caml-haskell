
module L = List
module Q = Queue
module H = Hashtbl

module OA = OnceAssoc
module T = Token
module LO = Layout
module SYN = Syntax
module PD = SYN.ParsedData
module ID = SYN.Identifier
module D = SYN.Decl
module M = SYN.Module
module CA = SYN.Case
module GD = SYN.Guard
module C = SYN.Constructor
module P = SYN.Pattern
module E = SYN.Expression


type e_module_type = (T.loc ID.id * M.export list * (M.impdecl list * E.t D.top list))

type 'module_e program_buffer = {
  pdata_assoc : (string, 'module_e PD.t) OA.t;
}

let lastLoadProgram = ref None

let load_program pdata_queue =
  let pa = OA.create
    (fun x -> "Already loaded module: " ^ x)
    (fun k pd -> pd.PD.local_module.PD.mname)
  in
  let _ = Q.iter (fun pdata -> pa.OA.add pdata.PD.local_module.PD.mname pdata) pdata_queue in
  let prog = { pdata_assoc = pa; } in
  let _ = (lastLoadProgram := Some prog) in
    prog

(* type 'module_e program_buffer = 'module_e PD.t *)

(* (T.loc ID.id * ) *)
type 'module_e eval_buffer = {
  sym_tab : (T.loc ID.id, 'module_e pre_value ref) H.t;
  program : 'module_e program_buffer;
}

and 'module_e env_t = 'module_e eval_buffer list

and 'module_e value =
    Bottom
  | IO
  | Literal of T.loc SYN.literal
  | Cons of C.con
  | Tuple of 'module_e pre_value list
  | List of 'module_e pre_value list
  | Closure of (P.pat list * E.t * 'module_e env_t) (* function or constructor *)
      (* arguemnt-pattern-list, expression, environment *)
  | Primitive of ('module_e value list -> 'module_e value)

and arg_exp = Exp of E.t | Atom of E.aexp

and 'module_e pre_value =
    Thunk of (P.pat * arg_exp * 'module_e env_t)
  | Thawed of 'module_e value

let gPrelude = ref (Some "Prelude")
let simple_cons name = Cons (C.App (ID.make_id_core name (ID.Qual gPrelude) T.implicit_loc, []))

let valTrue  = simple_cons "True"
let valFalse = simple_cons "False"

let primTable = 
  let t : (string, e_module_type value) H.t = H.create 32 in
  let err_pref = "Primitive Type error: " in
  let def_num_op2 name i64f floatf =
    H.add t name (Primitive (function
				 (Literal x) :: (Literal y) :: [] ->
				   begin
				     match (x, y) with
					 (SYN.Int (xi, _), SYN.Int (yi, _)) -> 
					   Printf.printf "DEBUG: called '%s' with %s %s\n" name (Int64.to_string xi) (Int64.to_string yi);
					   Literal (SYN.Int ((i64f xi yi), T.implicit_loc))
				       | (SYN.Int (xi, _), SYN.Float (yf, _)) -> Literal (SYN.Float ((floatf (Int64.to_float xi) yf), T.implicit_loc))
				       | (SYN.Float (xf, _), SYN.Int (yi, _)) -> Literal (SYN.Float ((floatf xf (Int64.to_float yi)), T.implicit_loc))
				       | (SYN.Float (xf, _), SYN.Float (yf, _)) -> Literal (SYN.Float ((floatf xf yf), T.implicit_loc))
				       | _ -> failwith (err_pref ^ name)
				   end
			       | _ -> failwith (err_pref ^ name))) in

  let _ = (def_num_op2 "+" Int64.add (+.),
	   def_num_op2 "-" Int64.sub (-.),
	   def_num_op2 "*" Int64.mul ( *.),
	   def_num_op2 "/" Int64.div (/.)) in

  let def_num_op2_bool name i64f floatf =
    H.add t name (Primitive (function
				 (Literal x) :: (Literal y) :: [] ->
				   if
				     begin
				       match (x, y) with
					   (SYN.Int (xi, _), SYN.Int (yi, _)) ->
					     Printf.printf "DEBUG: called '%s' with %s %s\n" name (Int64.to_string xi) (Int64.to_string yi);
					     i64f xi yi
					 | (SYN.Int (xi, _), SYN.Float (yf, _)) -> floatf (Int64.to_float xi) yf
					 | (SYN.Float (xf, _), SYN.Int (yi, _)) -> floatf xf (Int64.to_float yi)
					 | (SYN.Float (xf, _), SYN.Float (yf, _)) -> floatf xf yf
					 | _ -> failwith (err_pref ^ name)
				     end
				   then valTrue else valFalse

			       | _ -> failwith (err_pref ^ name))) in

  let _ = (def_num_op2_bool "<=" (<=) (<=),
	   def_num_op2_bool ">=" (>=) (>=),
	   def_num_op2_bool "==" (==) (==),
	   def_num_op2_bool "/=" (<>) (<>)) in
    (* H.add t "<=" (Primitive (function
				       (Literal x) :: (Literal y) :: [] ->
					 if
					   begin
					     match (x, y) with
						 (SYN.Int (xi, _), SYN.Int (yi, _)) ->
						   Printf.printf "DEBUG: called '<=' with %s %s\n" (Int64.to_string xi) (Int64.to_string yi);
						   xi <= yi
					       | (SYN.Int (xi, _), SYN.Float (yf, _)) -> (Int64.to_float xi) <= yf
					       | (SYN.Float (xf, _), SYN.Int (yi, _)) -> xf <= (Int64.to_float yi)
					       | (SYN.Float (xf, _), SYN.Float (yf, _)) -> xf <= yf
					       | _ -> failwith (err_pref ^ "<=")
					   end
					 then valTrue else valFalse

				     | _ -> failwith (err_pref ^ "<="))) in *)
				       
    
  let _ = H.add t "primError" (Primitive (function
					  (Literal (SYN.String m)) :: [] ->
					    failwith ("error: " ^ (fst m))
					| _ -> failwith (err_pref ^ "primError"))) in

  let _ = H.add t "print" (Primitive (function
					  (Literal (SYN.Int (i, _))) :: [] -> print_endline (Int64.to_string i); IO
					| (Literal (SYN.Float (f, _))) :: [] -> print_endline (string_of_float f); IO
					| (Literal (SYN.String (m, _))) :: [] -> print_endline m; IO
					| _ -> failwith (err_pref ^ "print"))) in
    t


let eval_buffer_create prog =
  { sym_tab = H.create 32; 
    program = prog; }

let env_top env = L.hd env

let env_top_symtab env = (env_top env).sym_tab

let env_create pd : 'module_e env_t =
  (eval_buffer_create pd) :: []

let env_get_prelude env =
  ((env_top env).program.pdata_assoc.OA.find "Prelude").PD.local_module

let local_env env =
  let top = env_top env in
  let n = H.copy top.sym_tab in
(*   let n = H.create 32 in *)
    { top with sym_tab = n} :: env

let mk_literal lit =
  Literal lit

let mk_closure env pat_list exp =
  Closure (pat_list, exp, env)

let lastErrAExp = ref None

let dump_aexp x =
  lastErrAExp := Some x;
  Std.dump x

let lastErrExp = ref None

let dump_exp x =
  lastErrExp := Some x;
  Std.dump x

let lastErrPat = ref None

(*
let lastErrEnv = ref None

let dump_pat_with_env x env =
  lastErrPat := Some x;
  lastErrEnv := Some env;
  Std.dump x
*)

let dump_pattern p =
  lastErrPat := Some p;
  Std.dump p

let applyClosureStack = Stack.create ()

let rec bind_id_core env id pv =
  let varref = ref pv in
  let _ = H.add (env_top_symtab env) (ID.unloc id) varref in
    varref

and make_thunk env pat arg_exp =
  match arg_exp with
      Exp (exp)   -> make_thunk_exp env pat exp 
    | Atom (aexp) -> make_thunk_atom_exp env pat aexp

and bind_pat env pat arg_exp  =
  bind_pat_with_thunk pat env (make_thunk env pat arg_exp)

and apply_id env id =
  H.find (env_top_symtab env) (ID.unloc id)

(*
and apply_pat env pat =
  let key = to_pat_for_hash pat in
  let rec match_rec env =
    match env with
	[] -> (failwith (Printf.sprintf "pattern not found when eval: %s" (dump_pat_with_env pat env)))
      | ebuf :: next_env ->
	  if H.mem ebuf.sym_tab key then H.find ebuf.sym_tab key
	  else
	    let _ = H.iter (fun p may_thunk -> ( * expanding pattern match * )
			      let varref = (eval_thunk_expand may_thunk) in
				if match_p p env varref then ()
				else failwith (Printf.sprintf "pattern not match: %s %s" (Std.dump p) (Std.dump varref))) ebuf.sym_tab in
	      if H.mem ebuf.sym_tab key then H.find ebuf.sym_tab key
	      else match_rec next_env
  in
    match_rec env
*)

and arity_list_take l n =
  let rec take_rec buf rest nn =
    match (nn, rest) with
	(0, _) -> (L.rev buf, rest)
      | (_, f::rest) -> take_rec (f::buf) rest (nn - 1)
      | (_, []) -> failwith
	  (Printf.sprintf "apply_closure: Too many arguemnt(s): expects %d argument(s), but is here applied to %d argument(s)"
	     (L.length l) n)
  in take_rec [] l n

and apply_closure caller_env closure arg_exp_list =
  match closure with
      Closure (apat_list, body_exp, env) ->
	Stack.push closure applyClosureStack;
	let (loc_env, ac) = (local_env env, L.length arg_exp_list) in
	let (pbind_list, apat_rest) = arity_list_take apat_list ac in
	let _  = L.map2 (fun pat arg_exp -> bind_pat loc_env pat arg_exp) pbind_list arg_exp_list in
	  if apat_rest = [] then eval_exp loc_env body_exp
	  else mk_closure loc_env apat_rest body_exp
    | Primitive (prim_fun) ->
	prim_fun (L.map (fun exp -> snd (eval_thunk (make_thunk caller_env P.WCardP exp))) arg_exp_list)
    | x -> failwith (Printf.sprintf "apply_closure: Not closure value: %s" (Std.dump x))

and make_thunk_atom_exp env pat =
  function
      E.VarE (_) as atom_exp -> Thunk (pat, Atom atom_exp, env)
    | E.ConsE (id) ->
	let v = Cons (C.App (id, [])) in Thawed v
	 
    | E.LiteralE (lit) -> let l = Literal lit in Thawed l

    | E.ParenE (exp) -> make_thunk_exp env pat exp

    | E.TupleE (_) as atom_exp -> Thunk (pat, Atom atom_exp, env)

    | E.ListE (_) as atom_exp -> Thunk (pat, Atom atom_exp, env)
    | x -> failwith (Printf.sprintf "aexp: Not implemented: %s" (dump_aexp x))

and eval_thunk pre_v =
  match pre_v with
      Thunk (pat, arg_exp, tenv) ->
	let v = (match arg_exp with
		     Exp e   -> eval_exp tenv e
		   | Atom ae -> eval_atom_exp tenv ae) in
	  (Some (pat, tenv), v)

    | Thawed v -> (None, v)


and eval_thunk_expand varref : 'a pre_value ref =
  match eval_thunk !varref with
      (Some (pat, tenv),  v) ->
	let must_true = match_p pat tenv v in
	let _ = assert must_true in
	  varref
    | (None, v) ->
	varref

(*
and eval_thunk (varref : 'a pre_value ref) =
  match !(eval_thunk_expand varref) with
      Thawed v -> v
    | _ -> failwith (Printf.sprintf "eval_thunk: Bug?: %s" (Std.dump varref))
*)

and eval_atom_exp env =
  function
      E.VarE (id) ->
	(if H.mem primTable id.ID.name then
	   (H.find primTable id.ID.name)
	 else
	   let varref = apply_id env id in
	     eval_thunk_expand varref)

    | E.ConsE (id) ->
	let v = Cons (C.App (id, [])) in v
	 
    | E.LiteralE (lit) -> let l = Literal lit in l

    | E.ParenE (exp) -> eval_exp env exp

    | E.TupleE (el) -> Tuple (L.map (fun e -> make_thunk_exp env P.WCardP e) el)

    | E.ListE (el) -> List (L.map (fun e -> make_thunk_exp env P.WCardP e) el)

    | x -> failwith (Printf.sprintf "aexp: Not implemented: %s" (dump_aexp x))

and eval_func_exp env =
  function
      E.FfunE aexp ->
	eval_atom_exp env aexp

    | E.FappE (fexp, aexp) -> 
	apply_closure env (eval_func_exp env fexp) [(Atom aexp)]

    | E.FappEID -> failwith ("BUG: E.FappEID found.")

and decl_list_local_env env eval_f decl_list =
  let loc_env = local_env env in
  let _ = L.map (fun decl -> eval_f loc_env decl) decl_list in
    loc_env

and eval_exp env =
  function
      E.Top (exp, _) -> eval_exp env exp

    | E.LambdaE (apat_list, exp) ->
	let c = mk_closure env apat_list exp in c
    | E.FexpE (E.FfunE (E.LiteralE lit)) ->
	let l = mk_literal lit in l
    | nv_exp ->
	(match nv_exp with
	   | E.FexpE fexp -> eval_func_exp env fexp

	   | E.VarOp2E (op, lexp, rexp) ->
	       apply_closure env (eval_atom_exp env (E.VarE op)) [(Exp lexp); (Exp rexp)]

	   | E.LetE (decl_list, exp) -> 
	       eval_exp (decl_list_local_env env eval_decl decl_list) exp

	   | E.IfE (pre_e, then_e, else_e) -> 
	       (match (eval_exp env pre_e) with
		    Cons(C.App (id, [])) when id.ID.name = "True" -> eval_exp env then_e
		  | Cons(C.App (id, [])) when id.ID.name = "False" -> eval_exp env else_e
		  | x  -> failwith (Printf.sprintf "exp: if: Type error %s" (Std.dump x)))
	   | E.CaseE (exp, []) ->
	       Bottom
	   | E.CaseE (exp, (CA.Simple (pat, case_exp, [])) :: alt_list) ->
	       let loc_env = local_env env in
	       let pv = bind_pat loc_env pat (Exp exp) in
		 if match_p pat loc_env (eval_thunk_expand (ref pv)) then
		   eval_exp loc_env case_exp
		 else
		   eval_exp env (E.Top (E.CaseE (exp, alt_list), None))

	   | x -> failwith (Printf.sprintf "exp: Not implemented: %s" (dump_exp x)))

and make_thunk_exp env pat =
  function
      E.Top (exp, _) -> make_thunk_exp env pat exp

    | E.LambdaE (apat_list, exp) ->
	let c = mk_closure env apat_list exp in
	  Thawed c
    | E.FexpE (E.FfunE (E.LiteralE lit)) ->
	let l = mk_literal lit in
	  Thawed l
    | nv_exp -> Thunk (pat, Exp nv_exp, env)

and pre_eval_rhs env rhs =
  let where_env w = match w with None -> env | Some dl -> (decl_list_local_env env eval_decl dl) in
  let (ev_exp, env) =
    match rhs with
	D.Rhs (exp, where) -> (exp, where_env where)
      | D.RhsWithGD (gdrhs_list, where) ->
	  (L.fold_right
	     (fun gdrhs else_e ->
		match gdrhs with
		    (GD.Guard gde, exp) ->
		      E.IfE (gde, exp, else_e))
	     gdrhs_list
	     (E.FexpE (E.FappE (E.FfunE (E.make_var_exp "error" (env_get_prelude env)), E.LiteralE (SYN.String ("Unmatched pattern", T.implicit_loc))))),
	   where_env where)
				 
(*       | x -> failwith (Printf.sprintf "rhs: Not implemented: %s" (Std.dump x)) *)
  in
    ((fun funlhs ->
	let _ = match funlhs with
	    D.FunDecLV (sym, apat_list) ->
	      bind_id_core env sym (Thawed (mk_closure env apat_list ev_exp))
	  | D.Op2Pat (op, (arg1, arg2)) ->
	      bind_id_core env op (Thawed (mk_closure env [arg1; arg2] ev_exp))
	  | x -> failwith (Printf.sprintf "funlhs: Not implemented: %s" (Std.dump x))
	in ()),
     (fun pat -> let _ = bind_pat env pat (Exp ev_exp) in () ))

and eval_gendecl env _ = ()

and eval_idecl env =
  function
      D.FunDecI (lhs, rhs) ->
	let (bfun, _) = pre_eval_rhs env rhs in
	  bfun lhs
    | D.BindI (id, rhs) ->
	let (_, bpat) = pre_eval_rhs env rhs in
	  bpat (P.VarP id)
    | D.EmptyI -> ()

and eval_cdecl env =
  function
      D.FunDecC (lhs, rhs) ->
	let (bfun, _) = pre_eval_rhs env rhs in
	  bfun lhs
    | D.BindC (id, rhs) ->
	let (_, bpat) = pre_eval_rhs env rhs in
	  bpat (P.VarP id)
    | D.GenDeclC gendecl -> eval_gendecl env gendecl

and eval_decl env =
  function
      D.FunDec (lhs, rhs) ->
	let (bfun, _) = pre_eval_rhs env rhs in
	  bfun lhs
    | D.PatFunDec (pat, rhs) ->
	let (_, bpat) = pre_eval_rhs env rhs in
	  bpat pat
    | D.GenDecl gendecl -> eval_gendecl env gendecl

(*     | x -> failwith (Printf.sprintf "decl: Not implemented: %s" (dump_decl x)) *)

and eval_topdecl env =
  function 
      D.Type (_) -> ()
    | D.Data (_) -> ()
    | D.NewType (_) -> ()
    | D.Class (_, _, _, cdecl_list) -> let _ = L.map (fun cd -> eval_cdecl env cd) cdecl_list in ()
    | D.Instance (_, _, _, idecl_list) -> let _ = L.map (fun instd -> eval_idecl env instd) idecl_list in ()
    | D.Default (_) -> ()
    | D.Decl d -> eval_decl env d
    (* | x -> failwith (Printf.sprintf "topdecl: Not implemented: %s" (dump_topdecl x)) *)

and eval_module env =
  function
(*       (x, y, (z, topdecl_list)) -> (x, y, (z, List.map (eval_topdecl env) topdecl_list)) *)
      (x, y, (z, topdecl_list)) ->
	let _ = List.map (eval_topdecl env) topdecl_list in ()

and eval_program env program =
  let _ = program.pdata_assoc.OA.iter (fun name pd ->
					 (* if name = "Prelude" then () else *)
					   eval_module env pd.PD.syntax) in
  let main_pd = program.pdata_assoc.OA.find "Main" in
    eval_atom_exp env (E.VarE (ID.make_id_core "main" (ID.Qual main_pd.PD.local_module.PD.mn_ref) T.implicit_loc))


(* Scan Pattern *)
and scan_pattern p =
  match p with
      P.PlusP (id, i64, _) ->
	(P.PlusP ((ID.unloc id), i64, T.implicit_loc),
	 ((fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern p))),
	  (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern p))))
	)
    | P.VarP (id) ->
	(P.VarP (ID.unloc id),
	 ((fun env thunk -> let _ = bind_id_core env id thunk in thunk),
	  (fun env varref -> (true, varref)))
	)
    | P.AsP (id, pat) ->
	(P.AsP (ID.unloc id, to_pat_for_hash pat),
	 ((fun env thunk ->
	     let _ = bind_id_core env id thunk in
	       bind_pat_with_thunk pat env thunk),
	  (fun env varref ->
	     let (p, sub_varref) = match_p pat env varref in
	     let _ = varref := !sub_varref in
	       (p, varref)))
	)
    | P.ConP (id, pat_list) ->
	(P.ConP (ID.unloc id, L.map to_pat_for_hash pat_list),
	 ((fun env thunk -> let _ = L.map (fun p -> bind_pat_with_thunk p env thunk) pat_list in thunk),
	  (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern p))))
	)
    | P.LabelP (id, fpat_list) ->
	(P.LabelP (ID.unloc id, L.map (fun (id, pat) -> (ID.unloc id, pat)) fpat_list),
	 ((fun env thunk -> let _ = L.map (fun (id, p) -> bind_pat_with_thunk p env thunk) fpat_list in thunk),
	  (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern p))))
	)
    | P.LiteralP literal ->
	(P.LiteralP (SYN.unloc_literal literal),
	 ((fun _ thunk -> thunk),
	  (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern p))))
	)
    | P.WCardP ->
	(P.WCardP,
	 ((fun _ thunk -> thunk),
	  (fun _ varref -> (true, varref)))
	)
    | P.TupleP pat_list ->
	(P.TupleP (L.map to_pat_for_hash pat_list),
	 ((fun env thunk -> let _ = L.map (fun p -> bind_pat_with_thunk p env thunk) pat_list in thunk),
	  (fun env varref ->
	     match eval_thunk !varref with
		 Tuple pre_vl ->
		   (L.fold_left2 (fun (snap_mp, Tuple snap) p pre_v ->
				    let (mp, result) = match_p p env pre_v in
				      ((snap_mp && mp), Tuple (result :: snap))) (true, Tuple [])  pat_list pre_vl)
	       | _ -> false))
	)
    | P.ListP pat_list ->
	(P.ListP (L.map to_pat_for_hash pat_list),
	 ((fun env thunk -> let _ = L.map (fun p -> bind_pat_with_thunk p env thunk) pat_list in thunk),
	  (fun env varref ->
	     match eval_thunk !varref with
		 List pre_vl ->
		   (L.fold_left2 (fun (snap_mp, List snap) p pre_v ->
				    let (mp, result) = match_p p env pre_v in
				      ((snap_mp && mp), List (result :: snap))) (true, List [])  pat_list pre_vl)
	       | _ -> false))
	)
    | P.MIntP (int64, _) ->
	(P.MIntP (int64, T.implicit_loc),
	 ((fun _ thunk -> thunk),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern p))))
	)
    | P.MFloatP (float, _) ->
	(P.MFloatP (float, T.implicit_loc),
	 ((fun _ thunk -> thunk),
	  (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern p))))
	)
    | P.Irref pat ->
	(P.Irref (to_pat_for_hash pat),
	 ((fun env thunk -> bind_pat_with_thunk pat env thunk),
	  (fun env varref -> match_p pat env varref))
	)

    (*     | P.Pat0 of pat op2list_patf *)
    (*     | P.Pat1 of pat op2list_patf *)

    | P.ConOp2P (id, pat1, pat2) ->
	(P.ConOp2P (ID.unloc id, (to_pat_for_hash pat1), (to_pat_for_hash pat2)),
	 ((fun env thunk -> let _ = (bind_pat_with_thunk pat1 env thunk, bind_pat_with_thunk pat2 env thunk) in thunk),
	  (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern p))))
	)

    | _ -> failwith ("Not converted Pat0 or Pat1 found. parser BUG!!")

and to_pat_for_hash p = fst (scan_pattern p)
and bind_pat_with_thunk p = fst (snd (scan_pattern p))
and match_p p = snd (snd (scan_pattern p))

let eval_test fn =
  let prog = load_program (LO.parse_files_with_prelude [fn]) in
    eval_program (env_create prog) prog
