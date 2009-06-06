
module L = List
module A = Array
module Q = Queue
module H = Hashtbl
module F = Printf

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

type 'module_e lambda = {
  arg_pat_list : P.pat list;
  body : E.t;
  env : 'module_e env_t;
  apply_where : ('module_e env_t -> 'module_e env_t);
}

and 'module_e closure =
  | SPat of ('module_e lambda)
  | MPat of ('module_e lambda list)
  | Prim of ('module_e thunk_type list -> 'module_e value)

and 'module_e value =
  | Bottom
  | IO
  | Literal of T.loc SYN.literal
  | Cons of (ID.id * ('module_e thunk_type list))
  | LabelCons of (ID.id * (ID.id, 'module_e thunk_type) OH.t )
  | Tuple of ('module_e thunk_type list)
  | List of ('module_e thunk_type list)
  | Closure of ('module_e closure * int * E.aexp list)


and 'module_e thunk_type = unit -> 'module_e value

and 'module_e pre_value =
    (* Thunk of (P.pat * E.t * 'module_e env_t) *)
    Thunk of (unit -> 'module_e value)
  | Thawed of 'module_e value


(* あるスコープでの環境 *)
and 'module_e eval_buffer = {
  sym_tab : (ID.id, 'module_e thunk_type) H.t;
  program : 'module_e program_buffer;
}

and 'module_e env_t = 'module_e eval_buffer list


let gPrelude = ref (Some "Prelude")
let simple_cons name = Cons (ID.make_id_core name (ID.Qual gPrelude), [])

let valTrue  = simple_cons "True"
let valFalse = simple_cons "False"

let primTable = 
  let table : (string, e_module_type value) H.t = H.create 32 in
  let raise_type_err name msg =
    failwith (F.sprintf "Primitive argument type error: %s: %s" name msg) in

  let mk_prim func arity = Closure (Prim (func), arity, []) in
  let bind_prim name prim = H.add table name prim in

  let def_eager_num_op2 name i64f floatf =
    bind_prim name
      (mk_prim (function
                     thxx :: thyy :: [] ->
                       begin
                         match (thxx (), thyy ()) with
                             ((Literal x), (Literal y)) ->
                               begin
                                 match (x, y) with
                                     (SYN.Int (xi, _), SYN.Int (yi, _)) -> 
                                       (* F.printf "DEBUG: called '%s' with %s %s\n" name (Int64.to_string xi) (Int64.to_string yi); *)
                                       Literal (SYN.Int ((i64f xi yi), T.implicit_loc))
                                   | (SYN.Int (xi, _), SYN.Float (yf, _)) -> Literal (SYN.Float ((floatf (Int64.to_float xi) yf), T.implicit_loc))
                                   | (SYN.Float (xf, _), SYN.Int (yi, _)) -> Literal (SYN.Float ((floatf xf (Int64.to_float yi)), T.implicit_loc))
                                   | (SYN.Float (xf, _), SYN.Float (yf, _)) -> Literal (SYN.Float ((floatf xf yf), T.implicit_loc))
                                   | _ -> raise_type_err name "Non-number argument found."
                               end
                           | _ -> raise_type_err name "Non-literal arguemnt found."
                       end
                   | _ -> raise_type_err name "Argument count is not 2.") 2) in

  let _ = (def_eager_num_op2 "+" Int64.add (+.),
           def_eager_num_op2 "-" Int64.sub (-.),
           def_eager_num_op2 "*" Int64.mul ( *.),
           def_eager_num_op2 "/" Int64.div (/.)) in

  let def_eager_num_op2_bool name i64f floatf =
    bind_prim name
      (mk_prim (function
                     thxx :: thyy :: [] ->
                       begin
                         match (thxx (), thyy ()) with
                             ((Literal x), (Literal y)) ->
                               if
                                 begin
                                   match (x, y) with
                                       (SYN.Int (xi, _), SYN.Int (yi, _)) ->
                                         (* F.printf "DEBUG: called '%s' with %s %s\n" name (Int64.to_string xi) (Int64.to_string yi); *)
                                         i64f xi yi
                                     | (SYN.Int (xi, _), SYN.Float (yf, _)) -> floatf (Int64.to_float xi) yf
                                     | (SYN.Float (xf, _), SYN.Int (yi, _)) -> floatf xf (Int64.to_float yi)
                                     | (SYN.Float (xf, _), SYN.Float (yf, _)) -> floatf xf yf
                                     | _ -> raise_type_err name "Non-number argument found."
                                 end
                               then valTrue else valFalse
                           | _ -> raise_type_err name "Non-literal arguemnt found."
                       end
                   | _ -> raise_type_err name "Argument count is not 2.") 2) in

  let _ = (def_eager_num_op2_bool "<=" (<=) (<=),
           def_eager_num_op2_bool ">=" (>=) (>=),
           def_eager_num_op2_bool "==" (==) (==),
           def_eager_num_op2_bool "/=" (<>) (<>)) in
                                       
  let prim_primError = "primError" in
  let _ = bind_prim prim_primError
    (mk_prim (function
                   th :: [] ->
                     begin
                       match th() with
                           Literal (SYN.String m) ->
                             failwith ("error: " ^ (fst m))
                         | _ -> raise_type_err prim_primError "Non-literal arguemnt found."
                     end
                 | _ -> raise_type_err prim_primError "Arguemnt not found.") 1) in

  let prim_print = "print" in
  let _ = bind_prim prim_print
    (mk_prim (function
                   th :: [] ->
                     begin
                       match th() with
                           Literal (SYN.Int (i, _)) -> print_endline (Int64.to_string i); IO
                         | Literal (SYN.Float (f, _)) -> print_endline (string_of_float f); IO
                         | Literal (SYN.String (m, _)) -> print_endline m; IO
                         | v -> raise_type_err prim_print ("Non-literal arguemnt found. " ^ (Std.dump v))
                     end
                 | _ -> raise_type_err prim_print "Arguemnt not found.") 1) in
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

let mk_lambda env pat_list exp where_env_fun =
  { arg_pat_list = pat_list;
    body = exp;
    env = env;
    apply_where = where_env_fun }

let mk_single_closure env pat_list exp where_env_fun =
  Closure (SPat (mk_lambda env pat_list exp where_env_fun),
           L.length pat_list,
           [])

let mk_lambda_closure env pat_list exp =
  mk_single_closure env pat_list exp (fun x -> x)

(* let mk_closure  *)

let lastErrAExp : E.aexp option ref = ref None

let dump_aexp x =
  lastErrAExp := Some x;
  Std.dump x

let lastErrExp : E.t option ref = ref None

let dump_exp x =
  lastErrExp := Some x;
  Std.dump x

let lastErrPat : P.pat option ref = ref None

let dump_pattern p =
  lastErrPat := Some p;
  Std.dump p

let applyClosureStack : e_module_type value Stack.t = Stack.create ()

(* let dummy_eval_exp (env : 'module_e env_t) (exp : E.t) =
  Bottom *)

(* let dummy_eval_func_exp (env : 'module_e env_t) (fexp : E.fexp) =
  Bottom *)

(* let dummy_eval_arg_exp (env : 'module_e env_t) (aexp : E.aexp) =
  Bottom *)

(* let eval_exp = dummy_eval_exp *)
(* let eval_func_exp = dummy_eval_func_exp *)
(* let eval_arg_exp = dummy_eval_arg_exp *)


(*let arity_list_take l n =
  let rec take_rec buf rest nn =
    match (nn, rest) with
        (0, _) -> (L.rev buf, rest)
      | (_, f::rest) -> take_rec (f::buf) rest (nn - 1)
      | (_, []) -> failwith
          (F.sprintf "apply_closure: Too many arguemnt(s): expects %d argument(s), but is here applied to %d argument(s)"
             (L.length l) n)
  in take_rec [] l n *)

let debug = false

let h_find err_fun =
  if debug then
    (fun ht k ->
       if H.mem ht k then
         H.find ht k
       else
         err_fun ())
  else H.find

let eval_id env id =
  h_find
    (fun () -> failwith (F.sprintf "eval_id: %s not found." (ID.name_str id)))
    (env_top_symtab env) id

let bind_thunk env id thunk =
  let _ = H.add (env_top_symtab env) id thunk in
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

(* Lazy pattern match against thunk *)
and bind_pat_with_thunk pat =
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
          (fun _ _ -> failwith (F.sprintf "Not implemented pattern match: %s" (dump_pattern pat)))

      | P.VarP (id, _) ->
          (fun env thunk ->
             let _ = bind_thunk env id thunk in (true, [thunk]))

      | P.AsP ((id, _), pat) ->
          (fun env thunk ->
             let (_, (matchp, tlist)) = (bind_thunk env id thunk,
                                         bind_pat_with_thunk pat env thunk)
             in (matchp, thunk :: tlist))

      | P.ConP ((id, _), pat_list) ->
          (fun env thunk ->
             let value = thunk ()
               (* コンストラクタにマッチする値かどうかを知るには
                  評価する必要がある *)
             in 
               match value with
                   Cons (cid, args) when cid = id
                     -> sub_patterns_match env pat_list args
                 | _ -> (false, [thunk]))

      | P.LabelP ((id, _), fpat_list) ->
          (fun env thunk ->
             let value = thunk () in
               match value with
                   LabelCons (cid, lmap) when cid = id ->
                     L.fold_left
                       (fun (matchp_sum, tlist_sum) ((label, _), pat) ->
                          let (matchp, tlist) = bind_pat_with_thunk pat env (OH.find lmap label) in
                            (matchp_sum & matchp, L.append tlist_sum tlist))
                       (true, [])
                       fpat_list
                 | _                                         -> (false, [thunk]))

      | P.LiteralP literal ->
          (fun _ thunk -> match thunk () with
               Literal expl when (SYN.eq_literal expl literal) -> (true, [thunk])
             | _                                               -> (false, [thunk]))

      | P.WCardP ->
          (fun _ thunk -> (true, [thunk]))

      | P.TupleP pat_list ->
          (fun env thunk ->
             let value = thunk () in
               match value with
                   Tuple (args) when (L.length args) = (L.length pat_list)
                     -> sub_patterns_match env pat_list args
                 | _ -> (false, [thunk]))

      | P.ListP pat_list ->
          (fun env thunk -> 
             let value = thunk () in
               match value with
                   List (args) when (L.length args) = (L.length pat_list)
                     -> sub_patterns_match env pat_list args
                 | _ -> (false, [thunk]))

(*
    | P.MIntP (int64, _) ->
        (fun _ thunk -> thunk)

    | P.MFloatP (float, _) ->
        (fun _ thunk -> thunk)

    | P.Irref pat ->
        (fun env thunk -> bind_pat_with_thunk pat env thunk)

    (*     | P.Pat0 of pat op2list_patf *)
    (*     | P.Pat1 of pat op2list_patf *)

    | P.ConOp2P (id, pat1, pat2) ->
        (fun env thunk -> let _ = (bind_pat_with_thunk pat1 env thunk, bind_pat_with_thunk pat2 env thunk) in thunk)

    | _ -> failwith ("Not converted Pat0 or Pat1 found. parser BUG!!")
*)
    | _ -> failwith "Not impelmented"

(* pattern_match : thunk を pattern にマッチ *)
and pattern_match local_env pat caller_env evalee =
  bind_pat_with_thunk pat local_env (make_exp_thunk caller_env evalee)
and pattern_match_arg_exp local_env pat caller_env evalee =
  bind_pat_with_thunk pat local_env (make_arg_exp_thunk caller_env evalee)

and apply_closure caller_env closure arg =
  (* let ... = *)
  match closure with
      Closure (clo, arity_count, args_rev) ->
        let args_rev = arg :: args_rev in
          begin
            match (L.length args_rev) with
                c when c < arity_count -> Closure (clo, arity_count, args_rev)
              | c when c > arity_count -> failwith "apply_closure: single: arity spill!"
              | _ -> (* (None, Some (clo, L.rev args_rev)) *)
                  let arg_exp_list = L.rev args_rev in
                    begin
                      match clo with
                        | SPat (lambda) ->
                            let loc_env = local_env lambda.env in
                              if (L.fold_left2
                                    (fun matchp pat arg_exp ->
                                       if matchp then let (matchp, _) = pattern_match_arg_exp loc_env pat caller_env arg_exp in matchp
                                       else false)
                                    true
                                    lambda.arg_pat_list
                                    arg_exp_list)
                              then eval_exp (lambda.apply_where loc_env) lambda.body
                              else failwith "apply_closure: single pattern not match"

                        | MPat (lambda_list) ->
                            L.fold_left
                              (fun result lmd ->
                                 match result with
                                   | Bottom ->
                                       let loc_env = local_env lmd.env in
                                         if (L.fold_left2
                                               (fun matchp pat arg_exp ->
                                                  if matchp then let (matchp, _) = pattern_match_arg_exp loc_env pat caller_env arg_exp in matchp
                                                  else false)
                                               true
                                               lmd.arg_pat_list
                                               arg_exp_list)
                                         then eval_exp (lmd.apply_where loc_env) lmd.body
                                         else failwith "apply_closure: all multi pattern not match"
                                   | result -> result)
                              Bottom
                              lambda_list

                        | Prim (prim_fun) ->
                            prim_fun (L.map (fun aexp -> (make_arg_exp_thunk caller_env aexp)) arg_exp_list)
                    end
          end
            
    | x -> failwith (F.sprintf "apply_closure: Not closure value: %s" (Std.dump x))

(* eval_* : expression から thunk へ *)
and eval_arg_exp env =
  function
      E.VarE ((id, _)) ->
        begin
          if H.mem primTable id.ID.name then
            H.find primTable id.ID.name
          else
            (* let _ = print_endline id.ID.name in *)
            let thunk = eval_id env id in
              thunk ()
        end

    | E.ConsE ((id, _)) ->
        let v = Cons (id, []) in v
         
    | E.LiteralE (lit) -> Literal lit

    | E.ParenE (exp) -> eval_exp env exp

    | E.TupleE (el) -> Tuple (L.map (fun e -> make_exp_thunk env e) el)

    | E.ListE (el) -> List (L.map (fun e -> make_exp_thunk env e) el)

    | x -> failwith (F.sprintf "aexp: Not implemented: %s" (dump_aexp x))


and eval_func_exp env =
  function
      E.FfunE aexp ->
        eval_arg_exp env aexp

    | E.FappE (fexp, aexp) -> 
        apply_closure env (eval_func_exp env fexp) aexp

    | E.FappEID -> failwith ("BUG: E.FappEID found.")

and decl_list_local_env env eval_f decl_list =
  let loc_env = local_env env in
  let _ = L.map (fun decl -> eval_f loc_env decl) decl_list in
    loc_env

and eval_exp env =
  function
      E.Top (exp, _) -> eval_exp env exp

    | E.LambdaE (apat_list, exp) ->
        let c = mk_lambda_closure env apat_list exp in c
    | E.FexpE (E.FfunE (E.LiteralE lit)) ->
        let l = mk_literal lit in l
    | nv_exp ->
        (match nv_exp with
           | E.FexpE fexp -> eval_func_exp env fexp

           | E.VarOp2E (op, lexp, rexp) ->
               apply_closure env
                 (apply_closure env (eval_arg_exp env (E.VarE op)) (E.ParenE lexp))
                 (E.ParenE rexp)

           | E.LetE (decl_list, exp) -> 
               eval_exp (decl_list_local_env env eval_decl decl_list) exp

           | E.IfE (pre_e, then_e, else_e) -> 
               (match (eval_exp env pre_e) with
                    Cons(id, []) when id.ID.name = "True" -> eval_exp env then_e
                  | Cons(id, []) when id.ID.name = "False" -> eval_exp env else_e
                  | x  -> failwith (F.sprintf "exp: if: Type error %s" (Std.dump x)))
           | E.CaseE (exp, []) ->
               Bottom
           | E.CaseE (exp, (CA.Simple (pat, case_exp, [])) :: alt_list) ->
               let loc_env = local_env env in
               let (match_p, tlist) = pattern_match loc_env pat env exp in
                 if match_p then
                   eval_exp loc_env case_exp
                 else
                   eval_exp env (E.Top (E.CaseE (exp, alt_list), None))

           | x -> failwith (F.sprintf "exp: Not implemented: %s" (dump_exp x)))

and expand_rhs env rhs =
  let where_env local_env = function
      None -> local_env
    | Some dl -> (decl_list_local_env local_env eval_decl dl) in
  let (ev_exp, new_local_env) =
    match rhs with
        D.Rhs (exp, where) -> (exp, (fun le -> where_env le where))
      | D.RhsWithGD (gdrhs_list, where) ->
          (L.fold_right
             (fun gdrhs else_e ->
                match gdrhs with
                    (GD.Guard gde, exp) ->
                      E.IfE (gde, exp, else_e))
             gdrhs_list
             (E.FexpE (E.FappE (E.FfunE (E.make_var_exp "error" (env_get_prelude env)), E.LiteralE (SYN.String ("Unmatched pattern", T.implicit_loc))))),
           (fun le -> where_env le where))
                                 
(*       | x -> failwith (F.sprintf "rhs: Not implemented: %s" (Std.dump x)) *)
  in
    ((fun funlhs ->
        match funlhs with
            D.FunLV ((sym, _), apat_list) ->
              (sym, apat_list, ev_exp, new_local_env)
          | D.Op2Fun ((op, _), (arg1, arg2)) ->
              (op, [arg1; arg2], ev_exp, new_local_env)
          | x -> failwith (F.sprintf "funlhs: Not implemented: %s" (Std.dump x))),
     (fun pat -> ignore (pattern_match env pat (new_local_env env) ev_exp)))

and eval_func_def env deflist =
  let (sym_opt, revr) = (L.fold_left 
                           (fun (sym_opt, revr) (funlhs, rhs) ->
                              let (cldfun, _) = expand_rhs env rhs in
                              let (sym, apat_list, ev_exp, new_local_env) = cldfun funlhs in
                                ((match sym_opt with
                                     None -> let arity = L.length apat_list in Some (sym, arity)
                                   | sym_opt -> sym_opt),
                                 ((mk_lambda env apat_list ev_exp new_local_env) :: revr)))
                           (None, [])
                           deflist) in
    begin
      match sym_opt with
          Some (sym, arity) -> let _ = bind_thunk env sym (make_thawed (Closure (MPat (L.rev revr), arity, []))) in ()
        | None -> failwith "decl: Bug function def is null list."
    end

and eval_gendecl env _ = ()

and eval_idecl env =
  function
      D.FunDecI deflist -> eval_func_def env deflist
    | D.BindI (id, rhs) ->
        let (_, bpat) = expand_rhs env rhs in
          bpat (P.VarP id)
    | D.EmptyI -> ()

and eval_cdecl env =
  function
      D.FunDecC deflist -> eval_func_def env deflist
    | D.BindC (id, rhs) ->
        let (_, bpat) = expand_rhs env rhs in
          bpat (P.VarP id)
    | D.GenDeclC gendecl -> eval_gendecl env gendecl

and eval_decl env =
  function
      D.FunDec deflist -> eval_func_def env deflist
    | D.PatBind (pat, rhs) ->
        let (_, bpat) = expand_rhs env rhs in
          bpat pat
    | D.GenDecl gendecl -> eval_gendecl env gendecl

let (lastEvalDecl : E.t D.decl option ref) = ref None

let eval_topdecl env tdecl =
  lastEvalDecl :=
    match tdecl with
        D.Type (_) -> None
      | D.Data (_) -> None
      | D.NewType (_) -> None
      | D.Class (_, _, _, cdecl_list) ->
          let _ = L.map (fun cd -> eval_cdecl env cd) cdecl_list in
            None
      | D.Instance (_, _, _, idecl_list) ->
          let _ = L.map (fun instd -> eval_idecl env instd) idecl_list in
            None
      | D.Default (_) -> None
      | D.Decl d ->
          let _ = eval_decl env d in
            Some d

let eval_module env =
  function
(*       (x, y, (z, topdecl_list)) -> (x, y, (z, List.map (eval_topdecl env) topdecl_list)) *)
      (x, y, (z, topdecl_list)) ->
        let _ = List.map (eval_topdecl env) topdecl_list in ()

(* eval_program : 
   全ての module を thunk tree に変換した後で
   toplevel環境 main シンボルに束縛されている thunk を展開 *)
let eval_program env program =
  let _ = program.pdata_assoc.OA.iter (fun name pd ->
                                         (* if name = "Prelude" then () else *)
                                           eval_module env pd.PD.syntax) in
    eval_arg_exp env (E.VarE (ID.idwl (ID.make_id "Main" "main") T.implicit_loc))


(*  *)
let eval_test fn =
  let prog = load_program (LO.parse_files_with_prelude [fn]) in
    eval_program (env_create prog) prog

(*
  (Eval.load_program (Eval.LO.parse_files_with_prelude [fn])).Eval.pdata_assoc.Eval.OA.find "Main"
*)
