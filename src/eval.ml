
module L = List
module A = Array
module Q = Queue
module H = Hashtbl

module OH = OrderedHash
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


type e_module_type = (ID.idwl * M.export list * (M.impdecl list * E.t D.top list))

(* プログラム全体 - プログラムはモジュールの集合 *)
type 'module_e program_buffer = {
  pdata_assoc : (string, 'module_e PD.t) OA.t;
}

let lastLoadProgram : e_module_type program_buffer option ref = ref None

let load_program pdata_queue =
  let pa = OA.create
    (fun x -> "Already loaded module: " ^ x)
    (fun k pd -> pd.PD.local_module.PD.mname)
  in
  let _ = Q.iter (fun pdata -> pa.OA.add pdata.PD.local_module.PD.mname pdata) pdata_queue in
  let prog = { pdata_assoc = pa; } in
  let _ = (lastLoadProgram := Some prog) in
    prog

type 'module_e value =
    Bottom
  | IO
  | Literal of T.loc SYN.literal
  | Cons of (ID.idwl * ('module_e thunk_type list))
  | LabelCons of (ID.idwl * (ID.idwl, 'module_e thunk_type) OH.t )
  | Tuple of ('module_e thunk_type list)
  | List of ('module_e thunk_type list)
  | Closure of (P.pat list * E.t * 'module_e env_t) (* function or constructor *)
      (* arguemnt-pattern-list, expression, environment *)
  | Primitive of (('module_e thunk_type list -> 'module_e value) * int)

(* and arg_exp = Exp of E.t | Atom of E.aexp *) (* E.make_aexp_exp : (E.aexp -> E.exp) *)

and 'module_e thunk_type = unit -> 'module_e value

and 'module_e pre_value =
    (* Thunk of (P.pat * E.t * 'module_e env_t) *)
    Thunk of (unit -> 'module_e value)
  | Thawed of 'module_e value


(* あるスコープでの環境 *)
and 'module_e eval_buffer = {
  sym_tab : (ID.idwl, 'module_e thunk_type) H.t;
  program : 'module_e program_buffer;
}

and 'module_e env_t = 'module_e eval_buffer list


let gPrelude = ref (Some "Prelude")
let simple_cons name = Cons (ID.make_id_core name (ID.Qual gPrelude) T.implicit_loc, [])

let valTrue  = simple_cons "True"
let valFalse = simple_cons "False"

let primTable = 
  let table : (string, e_module_type value) H.t = H.create 32 in
  let err_pref = "Primitive Type error: " in
  let bind_prim name prim = H.add table name prim in

  let def_eager_num_op2 name i64f floatf =
    bind_prim name
      (Primitive ((function
                       thxx :: thyy :: [] ->
                         begin
                           match (thxx (), thyy ()) with
                               ((Literal x), (Literal y)) ->
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
                             | _ -> failwith (err_pref ^ name)
                         end
                     | _ -> failwith (err_pref ^ name)), 2))
  in

  let _ = (def_eager_num_op2 "+" Int64.add (+.),
           def_eager_num_op2 "-" Int64.sub (-.),
           def_eager_num_op2 "*" Int64.mul ( *.),
           def_eager_num_op2 "/" Int64.div (/.)) in

  let def_eager_num_op2_bool name i64f floatf =
    bind_prim name
      (Primitive ((function
                       thxx :: thyy :: [] ->
                         begin
                           match (thxx (), thyy ()) with
                               ((Literal x), (Literal y)) ->
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
                             | _ -> failwith (err_pref ^ name)
                         end
                     | _ -> failwith (err_pref ^ name)), 2))
  in

  let _ = (def_eager_num_op2_bool "<=" (<=) (<=),
           def_eager_num_op2_bool ">=" (>=) (>=),
           def_eager_num_op2_bool "==" (==) (==),
           def_eager_num_op2_bool "/=" (<>) (<>)) in
                                       
  let _ = bind_prim "primError"
    (Primitive ((function
                     th :: [] ->
                       begin
                         match th() with
                             Literal (SYN.String m) ->
                               failwith ("error: " ^ (fst m))
                           | _ -> failwith (err_pref ^ "primError")
                       end
                   | _ -> failwith (err_pref ^ "primError")), 1)) in

  let _ = bind_prim "print"
    (Primitive ((function
                     th :: [] ->
                       begin
                         match th() with
                             Literal (SYN.Int (i, _)) -> print_endline (Int64.to_string i); IO
                           | Literal (SYN.Float (f, _)) -> print_endline (string_of_float f); IO
                           | Literal (SYN.String (m, _)) -> print_endline m; IO
                           | _ -> failwith (err_pref ^ "print")
                       end
                   | _ -> failwith (err_pref ^ "print")), 1)) in
    table



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
    { top with sym_tab = n } :: env

let mk_literal lit =
  Literal lit

let mk_closure env pat_list exp =
  Closure (pat_list, exp, env)


let lastErrAExp : E.aexp option ref = ref None

let dump_aexp x =
  lastErrAExp := Some x;
  Std.dump x

let lastErrExp : E.t option ref = ref None

let dump_exp x =
  lastErrExp := Some x;
  Std.dump x

let lastErrPat : P.pat option ref = ref None

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

let applyClosureStack : e_module_type value Stack.t = Stack.create ()

let dummy_eval_exp (env : 'module_e env_t) (exp : E.t) =
  Bottom

let dummy_eval_func_exp (env : 'module_e env_t) (fexp : E.fexp) =
  Bottom

let dummy_eval_arg_exp (env : 'module_e env_t) (aexp : E.aexp) =
  Bottom

(* let eval_exp = dummy_eval_exp *)
let eval_func_exp = dummy_eval_func_exp
(* let eval_arg_exp = dummy_eval_arg_exp *)


let arity_list_take l n =
  let rec take_rec buf rest nn =
    match (nn, rest) with
        (0, _) -> (L.rev buf, rest)
      | (_, f::rest) -> take_rec (f::buf) rest (nn - 1)
      | (_, []) -> failwith
          (Printf.sprintf "apply_closure: Too many arguemnt(s): expects %d argument(s), but is here applied to %d argument(s)"
             (L.length l) n)
  in take_rec [] l n

let eval_id env id =
  H.find (env_top_symtab env) (ID.unloc id)

let bind_thunk env id thunk =
  let _ = H.add (env_top_symtab env) (ID.unloc id) thunk in
    thunk

let thunk_value thunk =
  match thunk with
      Thunk (f) -> f ()
    | Thawed (v) -> v

let expand_thunk thunk_ref =
  match !thunk_ref with
      Thunk (_)  ->
        let v = thunk_value (!thunk_ref) in
        let _ = thunk_ref := Thawed v in
          v
    | Thawed (v) -> v

let make_thawed value =
  (fun () -> value)

let make_thunk eval_fun env evalee =
  let delay_fun = fun () -> (eval_fun env evalee) in
  let thunk_ref = ref (Thunk delay_fun) in
    fun () -> expand_thunk thunk_ref

let rec make_arg_exp_thunk env arg_exp =
  make_thunk eval_arg_exp env arg_exp

and make_exp_thunk env exp =
  make_thunk eval_exp env exp

(* Visitor for Pattern *)
and scan_pattern pat =
  let sub_patterns_match env pat_list thunk_list =
    L.fold_left2
      (fun (matchp_sum, tlist_sum) pat thunk ->
         let (matchp, tlist) = bind_pat_with_thunk pat env thunk in
           (matchp_sum & matchp, L.append tlist_sum tlist))
      (true, [])
      pat_list
      thunk_list
  in
  match pat with
      P.PlusP (id, i64, _) ->
        (P.PlusP ((ID.unloc id), i64, T.implicit_loc),
         ((fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern pat))),
          (* (fun _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern pat))) *) ()
         ))
    | P.VarP (id) ->
        (P.VarP (ID.unloc id),
         ((fun env thunk ->
             let _ = bind_thunk env id thunk in (true, [thunk])),
          (* (fun env varref -> (true, varref)) *) ()
         ))
    | P.AsP (id, pat) ->
        (P.AsP (ID.unloc id, path_hash pat),
         ((fun env thunk ->
             let (_, (matchp, tlist)) = (bind_thunk env id thunk,
                                         bind_pat_with_thunk pat env thunk)
             in (matchp, thunk :: tlist)),
          (* (fun env varref ->
             let (p, sub_varref) = match_p pat env varref in
             let _ = varref := !sub_varref in
             (p, varref)) *) ()
         ))
    | P.ConP (id, pat_list) ->
        (P.ConP (ID.unloc id, L.map path_hash pat_list),
         ((fun env thunk ->
             let value = thunk ()
               (* コンストラクタにマッチする値かどうかを知るには
                  評価する必要がある *)
             in 
               match value with
                   Cons (cid, args) when (ID.eq cid id)
                     -> sub_patterns_match env pat_list args
                 | _ -> (false, [thunk])),
          (* (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern pat))) *) ()
         ))
    | P.LabelP (id, fpat_list) ->
        (P.LabelP (ID.unloc id, L.map (fun (id, pat) -> (ID.unloc id, pat)) fpat_list),
         ((fun env thunk ->
             let value = thunk () in
               match value with
                   LabelCons (cid, lmap) when (ID.eq cid id) ->
                     L.fold_left
                       (fun (matchp_sum, tlist_sum) (label, pat) ->
                          let (matchp, tlist) = bind_pat_with_thunk pat env (OH.find lmap (ID.unloc label)) in
                            (matchp_sum & matchp, L.append tlist_sum tlist))
                       (true, [])
                       fpat_list
                 | _                                         -> (false, [thunk])),
          (* (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern pat))) *) ()
         ))
    | P.LiteralP literal ->
        (P.LiteralP (SYN.unloc_literal literal),
         ((fun _ thunk -> match thunk () with
               Literal expl when (SYN.eq_literal expl literal) -> (true, [thunk])
             | _                                               -> (false, [thunk])),
          (* (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern pat))) *) ()
         ))
    | P.WCardP ->
        (P.WCardP,
         ((fun _ thunk -> (true, [thunk])),
          (* (fun _ varref -> (true, varref)) *) ()
         ))
    | P.TupleP pat_list ->
        (P.TupleP (L.map path_hash pat_list),
         ((fun env thunk ->
             let value = thunk () in
               match value with
                   Tuple (args) when (L.length args) = (L.length pat_list)
                     -> sub_patterns_match env pat_list args
                 | _ -> (false, [thunk])),
          (* (fun env varref ->
             match eval_thunk !varref with
             Tuple pre_vl ->
                   (L.fold_left2 (fun (snap_mp, Tuple snap) p pre_v ->
                                    let (mp, result) = match_p p env pre_v in
                                      ((snap_mp && mp), Tuple (result :: snap))) (true, Tuple [])  pat_list pre_vl)
               | _ -> false) *) ()
         ))
    | P.ListP pat_list ->
        (P.ListP (L.map path_hash pat_list),
         ((fun env thunk -> 
             let value = thunk () in
               match value with
                   List (args) when (L.length args) = (L.length pat_list)
                     -> sub_patterns_match env pat_list args
                 | _ -> (false, [thunk])),
          (* (fun env varref ->
             match eval_thunk !varref with
                 List pre_vl ->
                   (L.fold_left2 (fun (snap_mp, List snap) p pre_v ->
                                    let (mp, result) = match_p p env pre_v in
                                      ((snap_mp && mp), List (result :: snap))) (true, List [])  pat_list pre_vl)
               | _ -> false) *) ()
         ))
(*
*)
(*
    | P.MIntP (int64, _) ->
        (P.MIntP (int64, T.implicit_loc),
         ((fun _ thunk -> thunk),
          (failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern pat))))
        )
    | P.MFloatP (float, _) ->
        (P.MFloatP (float, T.implicit_loc),
         ((fun _ thunk -> thunk),
          (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern pat))))
        )
    | P.Irref pat ->
        (P.Irref (path_hash pat),
         ((fun env thunk -> bind_pat_with_thunk pat env thunk),
          (fun env varref -> match_p pat env varref))
        )

    (*     | P.Pat0 of pat op2list_patf *)
    (*     | P.Pat1 of pat op2list_patf *)

    | P.ConOp2P (id, pat1, pat2) ->
        (P.ConOp2P (ID.unloc id, (path_hash pat1), (path_hash pat2)),
         ((fun env thunk -> let _ = (bind_pat_with_thunk pat1 env thunk, bind_pat_with_thunk pat2 env thunk) in thunk),
          (fun _ _ -> failwith (Printf.sprintf "Not implemented pattern match: %s" (dump_pattern pat))))
        )
    | _ -> failwith ("Not converted Pat0 or Pat1 found. parser BUG!!")
*)
    | _ -> failwith "Not impelmented"

and path_hash p = fst (scan_pattern p) (* rename from to_pat_for_hash *)
and bind_pat_with_thunk p = fst (snd (scan_pattern p))
(* and match_p p = snd (snd (scan_pattern p)) *)

(* pattern_match : thunk を pattern にマッチ *)
and pattern_match local_env pat caller_env evalee =
  bind_pat_with_thunk pat local_env (make_exp_thunk caller_env evalee)
and pattern_match_arg_exp local_env pat caller_env evalee =
  bind_pat_with_thunk pat local_env (make_arg_exp_thunk caller_env evalee)

and apply_closure caller_env closure arg_exp_list =
  match closure with
      Closure (apat_list, body_exp, env) ->
        Stack.push closure applyClosureStack;
        let (loc_env, ac) = (local_env env, L.length arg_exp_list) in
        let (pbind_list, apat_rest) = arity_list_take apat_list ac in
        let _  = L.map2 (fun pat arg_exp -> pattern_match_arg_exp loc_env pat caller_env arg_exp) pbind_list arg_exp_list in
          if apat_rest = [] then eval_exp loc_env body_exp
          else mk_closure loc_env apat_rest body_exp
    | Primitive (prim_fun, arity) ->
        let restc = arity - (L.length arg_exp_list) in
        let athunk_list = (L.map (fun aexp -> (make_arg_exp_thunk caller_env aexp)) arg_exp_list) in
          begin
            match restc with
                0                -> (prim_fun athunk_list)
              | _ when restc > 0 -> Primitive ((fun rest_list -> (* Primitive section *)
                                                  prim_fun (L.append athunk_list rest_list)), restc)
              | _                -> failwith (Printf.sprintf "Too many argument %d for this primitive" arity)
          end
    | x -> failwith (Printf.sprintf "apply_closure: Not closure value: %s" (Std.dump x))


(* eval_* : expression から thunk へ *)
and eval_arg_exp env =
  function
      E.VarE (id) ->
        begin
          if H.mem primTable id.ID.name then
            H.find primTable id.ID.name
          else
            let thunk = eval_id env id in
              thunk ()
        end

(*
    | E.ConsE (id) ->
        let v = Cons (id, [])) in v
*)
         
    | E.LiteralE (lit) -> Literal lit

    | E.ParenE (exp) -> eval_exp env exp

    | E.TupleE (el) -> Tuple (L.map (fun e -> make_exp_thunk env e) el)

    | E.ListE (el) -> List (L.map (fun e -> make_exp_thunk env e) el)

    | x -> failwith (Printf.sprintf "aexp: Not implemented: %s" (dump_aexp x))


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
               apply_closure env (eval_arg_exp env (E.VarE op)) [(E.ParenE lexp); (E.ParenE rexp)]

(*
           | E.LetE (decl_list, exp) -> 
               eval_exp (decl_list_local_env env eval_decl decl_list) exp
*)

           | E.IfE (pre_e, then_e, else_e) -> 
               (match (eval_exp env pre_e) with
                    Cons(id, []) when id.ID.name = "True" -> eval_exp env then_e
                  | Cons(id, []) when id.ID.name = "False" -> eval_exp env else_e
                  | x  -> failwith (Printf.sprintf "exp: if: Type error %s" (Std.dump x)))
           | E.CaseE (exp, []) ->
               Bottom
           | E.CaseE (exp, (CA.Simple (pat, case_exp, [])) :: alt_list) ->
               let loc_env = local_env env in
               let (match_p, tlist) = pattern_match loc_env pat env exp in
                 if match_p then
                   eval_exp loc_env case_exp
                 else
                   eval_exp env (E.Top (E.CaseE (exp, alt_list), None))

           | x -> failwith (Printf.sprintf "exp: Not implemented: %s" (dump_exp x)))

(*
*)

(* eval_program : 
   全ての module を thunk tree に変換した後で
   toplevel環境 main シンボルに束縛されている thunk を展開 *)

