(* Scan Pattern *)
let rec scan_pattern p =
  match p with
      P.PlusP (id, i64, _) ->
	(P.PlusP ((ID.unloc id), i64, T.implicit_loc),
	 ((fun a_id -> (ID.unloc a_id) <> id),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))
    | P.VarP (id) ->
	(P.VarP (ID.unloc id),
	 ((fun a_id -> (ID.unloc a_id) <> id),
	  (fun env exp ->
	     let _ = bind_pat env (P.VarP (id)) (Thawed (eval_exp env exp)) in
	       true
	  )))
    | P.AsP (id, pat) ->
	(P.AsP (ID.unloc id, to_pat_for_hash pat),
	 ((fun a_id ->
	     (ID.unloc a_id) <> id && fun_fv_p pat id),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))
    | P.ConP (id, pat_list) ->
	(P.ConP (ID.unloc id, L.map to_pat_for_hash pat_list),
	 ((fun a_id ->
	     (ID.unloc a_id) <> id && L.fold_left (fun b pat -> b && fun_fv_p pat a_id) true pat_list),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))
    | P.LabelP (id, fpat_list) ->
	(P.LabelP (ID.unloc id, L.map (fun (id, pat) -> (ID.unloc id, pat)) fpat_list),
	 ((fun a_id ->
	     (ID.unloc a_id) <> id && L.fold_left (fun b (fvar, pat) -> b && fun_fv_p pat a_id) true fpat_list),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))
    | P.LiteralP literal ->
	(P.LiteralP (SYN.unloc_literal literal),
	 ((fun _ -> true),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))
    | P.WCardP ->
	(P.WCardP,
	 ((fun _ -> true),
	  (fun _ _ -> true)))
    | P.TupleP pat_list ->
	(P.TupleP (L.map to_pat_for_hash pat_list),
	 ((fun a_id -> L.fold_left (fun b pat -> b && fun_fv_p pat a_id) true pat_list),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))
    | P.ListP pat_list ->
	(P.ListP (L.map to_pat_for_hash pat_list),
	 ((fun a_id -> L.fold_left (fun b pat -> b && fun_fv_p pat a_id) true pat_list),
	  (fun env exp ->
	     let v = eval_exp env exp in
	       match v with
		   List pre_vl ->
		     let _ = L.map2 (fun pat pre_v -> bind_pat env pat pre_v) pat_list pre_vl in
		       true
		 | _ -> false
	  )))
    | P.MIntP (int64, _) ->
	(P.MIntP (int64, T.implicit_loc),
	 ((fun _ -> true),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))
    | P.MFloatP (float, _) ->
	(P.MFloatP (float, T.implicit_loc),
	 ((fun _ -> true),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))
    | P.Irref pat ->
	(P.Irref (to_pat_for_hash pat),
	 (fun_fv_p pat,
	  (fun env exp ->
	     bind_pat env pat (Thunk (exp, env));
	     true)))

    (*     | P.Pat0 of pat op2list_patf *)
    (*     | P.Pat1 of pat op2list_patf *)

    | P.ConOp2P (id, pat1, pat2) ->
	(P.ConOp2P (ID.unloc id, (to_pat_for_hash pat1), (to_pat_for_hash pat2)),
	 ((fun a_id -> fun_fv_p pat1 a_id && fun_fv_p pat2 a_id),
	  (failwith (Printf.sprintf "Not implemented pattern match: %s" (Std.dump p)))))

    | _ -> failwith ("Not converted Pat0 or Pat1 found. parser BUG!!")

and to_pat_for_hash p = fst (scan_pattern p)
and fun_fv_p p = fst (snd (scan_pattern p))
and match_p p = snd (snd (scan_pattern p))

(* Scan Free Variable *)

and arg_pat_list =
  function
      D.FunDecLV (fnsym, plist) ->
	(P.VarP fnsym) :: plist
    | D.Op2Pat (opsym, (pleft, pright)) ->
	[(P.VarP opsym); pleft; pright]
    | D.NestDec (funlhs, plist) ->
	L.rev_append plist (arg_pat_list funlhs)

and fv_exp pdata aplist =
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
	if L.fold_left (fun b pat -> b && fun_fv_p pat id) true aplist then [id]
	else []
    | x -> failwith "fv: atom_exp: Not implemented."

and fv_decl pdata aplist =
  function
      D.FunDec (lhs, D.Rhs (exp, None)) ->
	fv_exp pdata (L.rev_append aplist (arg_pat_list lhs)) exp
    | D.PatFunDec (pat, D.Rhs (exp, None)) ->
	fv_exp pdata (pat :: aplist) exp
    | x -> failwith (Printf.sprintf "fv: decl: Not implemented:\n%s" (Std.dump x))


