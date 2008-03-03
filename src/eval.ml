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
  pat_t : (P.pat, E.t) H.t;
  fun_t : (E.t D.funlhs, E.t) H.t;
}

type env = eval_buffer list

let eval_buffer_create () =
  { pat_t = H.create 32;
    fun_t = H.create 32;  }

let new_scope env =
  (eval_buffer_create ()) :: env

let env_create () : env =
  new_scope []


let patt env =
  (L.hd env).pat_t

let bindp env pat exp =
  H.add (patt env) (P.to_pat_for_hash pat) exp

let bindf env funlhs exp =
  H.add (L.hd env).fun_t funlhs exp

let queryp env pat =
  H.find (patt env) (P.to_pat_for_hash pat)


let rec eval_exp pdata env =
  function
      E.Top (E.VarOp2E (op, lexp, rexp), None) ->
	applyf pdata env [lexp; rexp] (queryp env (P.VarP op))
    | E.Top (E.LambdaE (apat_list, exp), None) -> ()
    | E.Top (E.LetE (decl_list, exp), None) -> 
	let env = new_scope env in
	let _ = L.map (fun decl -> eval_decl pdata env decl) decl_list in
	  ()
    | E.Top (E.IfE (pre_e, then_e, else_e), None) -> 
	let _ = (eval_exp pdata env pre_e,
		 eval_exp pdata env then_e,
		 eval_exp pdata env else_e) in
	  ()
    | E.Top (E.CaseE (exp, (CA.WithGD (pat, _, _)) :: alt_list), None) ->
	let env = new_scope env in
	  bindp env pat exp
    | x -> failwith (Printf.sprintf "exp: Not implemented:\n%s" (Std.dump x))

and applyf pdata env aexp_list (E.LambdaE (apat_list, exp)) =
  let env = new_scope env in
  let _  = L.map2 (fun pat exp -> bindp env pat exp) apat_list aexp_list in
    eval_exp pdata env exp


and eval_rhs pdata env =
  function
      D.Rhs (exp, None) ->
	((fun funlhs ->
	    let _ = match funlhs with
		D.FunDecLV (sym, apat_list) ->
		  bindp env (P.VarP sym) (E.LambdaE (apat_list, exp))
	      | D.Op2Pat (op, (arg1, arg2)) ->
		  bindp env (P.VarP op) (E.LambdaE ([arg1; arg2], exp))
	      | x -> failwith (Printf.sprintf "rhs1: Not implemented:\n%s" (Std.dump x))
	    in
	      eval_exp pdata env exp),
	 (fun pat ->
	    bindp env pat exp;
	    eval_exp pdata env exp))
(*     | D.Rhs (exp, Some exp_decl_list) -> *)
    | x ->
	failwith (Printf.sprintf "rhs0: Not implemented:\n%s" (Std.dump x))

and eval_decl pdata env =
  function
      D.FunDec (lhs, (D.Rhs (exp, None) as rhs)) ->
	let (bf, _) = eval_rhs pdata env rhs in
	  bf lhs
    | D.PatFunDec (pat, (D.Rhs (exp, None) as rhs)) ->
	let (_, bp) = eval_rhs pdata env rhs in
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


let eval_test fn =
  let pdata = LO.parse_test fn in
    eval_module pdata (env_create ()) pdata.PD.syntax
