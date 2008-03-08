module LO = Layout
module SYN = Syntax
module PD = SYN.ParsedData
module ID = SYN.Identifier
module H = Hashtbl
module D = SYN.Decl
module CA = SYN.Case
module P = SYN.Pattern
module E = SYN.Expression
(* module S = Stack *)
module L = List


type eval_buffer = {
  pat_t : (P.pat, value) H.t;
}

and env = eval_buffer list

and value =
    Bottom
  | True
  | False
  | Value of E.t
  | Unevaled of E.t
  | Closure of (P.pat list * P.pat list * E.t)
      (* arguemnt-pattern-list, free-variable-list, expression *)

let eval_buffer_create () =
  { pat_t = H.create 32; }

let new_scope env =
  (eval_buffer_create ()) :: env

let env_create () : env =
  new_scope []


let env_top env =
  (L.hd env).pat_t

let local_env env =
  let top = env_top env in
  let n = H.copy top in
    { pat_t = n} :: env

let bindp env pat value =
  H.add (env_top env) (P.to_pat_for_hash pat) value

let queryp env pat =
  H.find (env_top env) (P.to_pat_for_hash pat)


let rec arg_pat_list =
  function
      D.FunDecLV (fnsym, plist) ->
	(P.VarP fnsym) :: plist
    | D.Op2Pat (opsym, (pleft, pright)) ->
	[(P.VarP opsym); pleft; pright]
    | D.NestDec (funlhs, plist) ->
	L.rev_append plist (arg_pat_list funlhs)

let rec fv_exp pdata aplist =
  function
      E.Top (E.VarOp2E (op, lexp, rexp), None) ->
	L.rev_append (fv_exp pdata aplist lexp) (fv_exp pdata aplist rexp)
    | E.Top (E.LambdaE (apat_list, exp), None) ->
	fv_exp pdata (L.rev_append aplist apat_list) exp
    | E.Top (E.LetE (decl_list, exp), None) ->
	L.fold_left (fun l decl -> L.rev_append l (fv_decl pdata aplist decl)) [] decl_list
    | E.Top (E.IfE (pre_e, then_e, else_e), None) ->
	L.rev_append
	  (fv_exp pdata aplist pre_e)
	  (L.rev_append
	     (fv_exp pdata aplist then_e)
	     (fv_exp pdata aplist else_e))
(*     | E.Top (E.CaseE (exp, (CA.WithGD (pat, _, _)) :: alt_list), None) -> *)
    | E.Top (E.CaseE (exp, [(CA.Simple (pat, _, _))]), None) ->
	fv_exp pdata (pat :: aplist) exp
    | E.Top (E.FexpE fexp, None) ->
	fv_fun_exp pdata aplist fexp
    | x -> failwith (Printf.sprintf "fv: exp: Not implemented : %s" (Std.dump x))

and fv_fun_exp pdata aplist =
  function
      E.FappE (fexp, aexp) ->
	L.rev_append
	  (fv_fun_exp pdata aplist fexp)
	  (fv_atom_exp pdata aplist aexp)
    | E.FfunE (aexp) ->
	(fv_atom_exp pdata aplist aexp)
    | x -> failwith (Printf.sprintf "fv: fun_exp: Not converted fexp found. parser BUG! : %s" (Std.dump x))

and fv_atom_exp pdata aplist =
  function
      E.VarE (id) ->
	if L.fold_left (fun b pat -> b && P.fun_fv_p pat id) true aplist then [id]
	else []
    | x -> failwith "fv: atom_exp: Not implemented."

and fv_decl pdata aplist =
  function
      D.FunDec (lhs, D.Rhs (exp, None)) ->
	fv_exp pdata (L.rev_append aplist (arg_pat_list lhs)) exp
    | D.PatFunDec (pat, D.Rhs (exp, None)) ->
	fv_exp pdata (pat :: aplist) exp
    | x -> failwith (Printf.sprintf "fv: decl: Not implemented:\n%s" (Std.dump x))

let mk_unevaled exp =
  ref (Unevaled exp)

let mk_closure pdata pat_list exp =
  ref (Closure (pat_list, L.map (fun id -> P.VarP id) (fv_exp pdata pat_list exp), exp))


let rec apply_closure pdata env aexp_list =
  function
      Closure (apat_list, fvpat_list, exp) ->
	let loc_env = local_env env in
	let _  = L.map2 (fun pat exp -> bindp loc_env pat (eval_exp pdata env exp)) apat_list aexp_list in
	  eval_exp pdata loc_env exp
    | x -> failwith (Printf.sprintf "applyf: Invalid function application: %s" (Std.dump x))


and eval_exp pdata env =
  function
      E.Top (E.VarOp2E (op, lexp, rexp), None) ->
	apply_closure pdata env [lexp; rexp] (queryp env (P.VarP op))
    | E.Top (E.LambdaE (apat_list, exp), None) ->
	Closure (apat_list, [], exp)
    | E.Top (E.LetE (decl_list, exp), None) -> 
	let loc_env = local_env env in
	let _ = L.map (fun decl -> eval_decl pdata loc_env decl) decl_list in
	  eval_exp pdata loc_env exp
    | E.Top (E.IfE (pre_e, then_e, else_e), None) -> 
	(match (eval_exp pdata env pre_e) with
	     True -> eval_exp pdata env then_e
	   | False -> eval_exp pdata env else_e
	   | _  -> Bottom)
    | E.Top (E.CaseE (exp, []), None) ->
	Bottom
    | E.Top (E.CaseE (exp, (CA.Simple (pat, case_exp, [])) :: alt_list), None) ->
	let loc_env = local_env env in
	  (match bindp loc_env pat (eval_exp pdata env exp) with
	       Bottom -> eval_exp pdata env (E.Top (E.CaseE (exp, alt_list), None))
	     | x -> x)
    | x -> failwith (Printf.sprintf "exp: Not implemented:\n%s" (Std.dump x))

and pre_eval_rhs pdata env =
  function
      D.Rhs (exp, None) ->
	((fun funlhs ->
	    let _ = match funlhs with
		D.FunDecLV (sym, apat_list) ->
		  bindp env (P.VarP sym) (mk_closure pdata apat_list exp)
	      | D.Op2Pat (op, (arg1, arg2)) ->
		  bindp env (P.VarP op) (mk_closure pdata [arg1; arg2] exp)
	      | x -> failwith (Printf.sprintf "rhs1: Not implemented:\n%s" (Std.dump x))
	    in
	      eval_exp pdata env exp),
	 (fun pat ->
	    bindp env pat (mk_unevaled exp);
	    eval_exp pdata env exp))
(*     | D.Rhs (exp, Some exp_decl_list) -> *)
    | x ->
	failwith (Printf.sprintf "rhs0: Not implemented:\n%s" (Std.dump x))

and eval_decl pdata env =
  function
      D.FunDec (lhs, (D.Rhs (exp, None) as rhs)) ->
	let (bf, _) = pre_eval_rhs pdata env rhs in
	  bf lhs
    | D.PatFunDec (pat, (D.Rhs (exp, None) as rhs)) ->
	let (_, bp) = pre_eval_rhs pdata env rhs in
	  bp pat
    | x -> failwith (Printf.sprintf "decl: Not implemented:\n%s" (Std.dump x))

and eval_topdecl pdata env =
  function 
      D.Decl d -> eval_decl pdata env d
    | x -> failwith (Printf.sprintf "topdecl: Not implemented:\n%s" (Std.dump x))

and eval_module pdata env =
  function
(*       (x, y, (z, topdecl_list)) -> (x, y, (z, List.map (eval_topdecl pdata env) topdecl_list)) *)
      (x, y, (z, topdecl_list)) -> List.map (eval_topdecl pdata env) topdecl_list


(* 
let eval_test fn =
  let pdata = LO.parse_test fn in
    eval_module pdata (env_create ()) pdata.PD.syntax
*)

