
module L = List
module A = Array
module Q = Queue
module H = Hashtbl
module F = Printf

module OH = OrderedHash
module T = Token
module S = Symbol
module LO = Layout
module SYN = Syntax
module ID = SYN.Identifier
module D = SYN.Decl
module M = SYN.Module
module CA = SYN.Case
module GD = SYN.Guard
module C = SYN.Constructor
module P = SYN.Pattern
module E = SYN.Expression

module SYA = SYN.All

let create_symtab () = H.create 32

type export_buffer = {
  export_module : (S.t, bool) H.t;
  export : (S.t, bool) H.t;
}

let export_buffer () = {
  export_module = create_symtab ();
  export = create_symtab ();
}

let export_export_module exbuf = exbuf.export_module
let export_export exbuf = exbuf.export

type syntax_tree_t = (ID.symwl * M.export list * (M.impdecl list * E.t D.top list))

type lambda_t = {
  arg_pat_list : P.pat list;
  body : E.t;
  lambda_env : env_t;
  apply_where : (env_t -> env_t);
}

and closure_t =
  | SPat of (lambda_t)
  | MPat of (lambda_t list)
  | Prim of (thunk_t list -> value_t)

and value_t =
  | Bottom
  | IO
  | Literal of SYN.literal
  | Cons of (ID.id * (thunk_t list))
  | LabelCons of (ID.id * (ID.id, thunk_t) OH.t )
  | Tuple of (thunk_t list)
  | List of (thunk_t list)
  | Closure of (closure_t * int * E.aexp list)

and thunk_t = unit -> value_t

and pre_value_t =
  | Thunk of (unit -> value_t) (* thunk_t と同じ型になっているのは偶然であることに注意 *)
  | Thawed of value_t

and scope_t = (S.t, thunk_t) H.t

(* あるスコープでの環境 *)
and env_t = {
  symtabs : (scope_t) list;
  top_scope : scope_t;
}

let env_create syntax : env_t =
  let top = create_symtab () in
  let env =
    {
      symtabs = [ top ];
      top_scope = top;
    }
  in
    env

let env_tablist env = env.symtabs
let env_symtab env = L.hd (env_tablist env)
let env_top_symtab env =
  env.top_scope

let local_env env =
  let tab = env.symtabs in
  let n = H.copy (L.hd tab) in
  let new_env = { env with
                    symtabs = n :: tab;
                } in
    new_env

type import_module_t = (M.qual * S.t * S.t option * M.impspec option)

(* モジュールの評価環境 *)
type 'syntax_tree module_buffer = {
  code : 'syntax_tree;
  env : env_t;
  import_module : (S.t, import_module_t) H.t;
  fixity : (S.t, SYN.fixity * S.t option) H.t;
}

let module_buffer syntax = {
  code = syntax;
  env = env_create syntax;
  import_module = create_symtab ();
  fixity = create_symtab ();
}

(* *)

let module_code modbuf = modbuf.code
let module_env modbuf = modbuf.env
let module_import_module modbuf = modbuf.import_module
let module_fixity modbuf = modbuf.fixity
(* let import_module modbuf = modbuf.import *)

(* プログラム全体の評価環境 - プログラムはモジュールの集合 *)
type 'syntax_tree program_buffer = (S.t, 'syntax_tree module_buffer) SaHt.t

let program_module_buffer program modsym =
  SaHt.find program modsym

let qualified_sym q n =
  S.intern ((S.name q) ^ "." ^ (S.name n))

(* let program_op2fixity program id = *)
(*   let ID.short id *)

let lastLoadProgram : syntax_tree_t program_buffer option ref = ref None

let load_program syntax_list =
  let prog = SaHt.create
    S.name
    (fun _ -> "<mod>")
    (Some (fun x -> "Already loaded module (before fixity resolve): " ^ x))
    None (* (fun ks vs -> ks ^ " => " ^ vs) *)
    "<program buffer before fixity resolve>"
  in
  let _ = L.iter (fun (((modsym, _), _, _) as syntax) ->
                    SaHt.add prog modsym (module_buffer syntax)) syntax_list in
  let _ = (lastLoadProgram := Some prog) in
    prog

let default_fixity = (SYN.default_op_fixity, None)

let h_find_fixity =
  (fun ht k ->
     if H.mem ht k then  H.find ht k
     else default_fixity)

let eval_op2_fixity modbuf id =
  let ftab = module_fixity modbuf in
    match ID.qual id with
      | ID.Q m ->
          let long = ID.long_sym id in
            h_find_fixity ftab long
      | _ ->
          let short = (ID.short_sym id) in
            h_find_fixity ftab short

let bind_op2_fixity modbuf id ((fixity, tcls) as op2) =
  let ftab = module_fixity modbuf in
  let _ = (H.add ftab (ID.long_sym id) op2,
           H.add ftab (ID.short_sym id) op2) in
    ()

let global_fixity program modsym sym =
  let modbuf = program_module_buffer program modsym in
  let ftab = module_fixity modbuf in
    h_find_fixity ftab sym

let bind_import_fixity ftab program is_qual modsym sym fixity =
  (* let _ = F.printf "DEBUG: bind_fixity: modsym %s sym %s\n" (S.name modsym) (S.name sym) in *)
  let _ = if not is_qual then H.add ftab sym fixity in
    H.add ftab (qualified_sym modsym sym) fixity

let list2term_func modbuf =
  
  let rec patlist2term min_i func list =
    let pat_fun = SYA.maptree_pat func in

    let rec fold_leafs list =
      let scanned_op2pat op patAA patBB =
        P.ConOp2P (op,
                   pat_fun patAA,
                   pat_fun patBB) in
        
        match list with
          | P.PatF (pat, P.Op2End) ->
              P.uni_pat (pat_fun pat)
          | P.PatF (patAA, P.Op2F (op_aa_wl, (P.PatF (patBB, P.Op2End)))) ->
              P.uni_pat (scanned_op2pat op_aa_wl patAA patBB)
          | P.PatF (patAA, P.Op2F ((op_aa, _) as op_aa_wl, ((P.PatF (patBB, P.Op2F ((op_bb, _) as op_bb_wl, rest))) as cdr))) ->
              begin
                let (aa_fixity, _) = eval_op2_fixity modbuf op_aa in
                let (bb_fixity, _) = eval_op2_fixity modbuf op_bb in
                  match (aa_fixity, bb_fixity) with
                      ((_, aa_i), _) when aa_i < min_i ->
                        failwith (F.sprintf "Pat%d cannot involve fixity %s operator." min_i (SYN.fixity_str aa_fixity))
                    | (_, (_, bb_i)) when bb_i < min_i ->
                        failwith (F.sprintf "Pat%d cannot involve fixity %s operator." min_i (SYN.fixity_str bb_fixity))
                    | ((_, aa_i), (_, bb_i)) when aa_i > bb_i ->
                        fold_leafs (P.patf_cons (scanned_op2pat op_aa_wl patAA patBB) op_bb_wl rest)
                    | ((SYN.InfixLeft, aa_i), (SYN.InfixLeft, bb_i)) when aa_i = bb_i ->
                        fold_leafs (P.patf_cons (scanned_op2pat op_aa_wl patAA patBB) op_bb_wl rest)
                    | ((_, aa_i), (_, bb_i)) when aa_i < bb_i ->
                        P.patf_cons patAA op_aa_wl (fold_leafs cdr)
                    | ((SYN.InfixRight, aa_i), (SYN.InfixRight, bb_i)) when aa_i = bb_i ->
                        P.patf_cons patAA op_aa_wl (fold_leafs cdr)
                    | _ ->
                        failwith (F.sprintf "Syntax error for operation priority. left fixity %s, right fixity %s"
                                    (SYN.fixity_str aa_fixity)
                                    (SYN.fixity_str bb_fixity))
              end
          | _ -> failwith "Arity 2 operator pattern syntax error."
    in
      match fold_leafs list with
        | P.PatF (pat, P.Op2End) -> pat
        | P.PatF (pat, P.Op2F (_, P.Op2NoArg)) -> failwith "patlist2term: section not implemented."
        | folded -> patlist2term min_i func folded
  in

  let rec explist2term func list =
    let exp10_fun = SYA.maptree_exp10 func in

    let rec fold_leafs list =
      let scanned_op2exp op expAA expBB =
        E.VarOp2E (op,
                   exp10_fun expAA,
                   exp10_fun expBB) in
        match list with
          | E.ExpF (exp, E.Op2End) -> (* list *)
              E.uni_exp (exp10_fun exp)
          | E.ExpF (expAA, E.Op2F (op_aa,
                                   (E.ExpF (expBB, E.Op2End)))) ->
              E.uni_exp (scanned_op2exp op_aa expAA expBB)
          | E.ExpF (expAA, E.Op2F ((op_aa, _) as op_aa_wl,
                                   ((E.ExpF (expBB, E.Op2F ((op_bb, _) as op_bb_wl, rest))) as cdr))) ->
              begin
                let (aa_fixity, _) = eval_op2_fixity modbuf op_aa in
                let (bb_fixity, _) = eval_op2_fixity modbuf op_bb in
                  (* F.printf "(%s, %d) vs (%s, %d)\n" (ID.name_str op_aa) (snd aa_fixity) (ID.name_str op_bb) (snd bb_fixity); *)
                  match (aa_fixity, bb_fixity) with
                    | ((_, aa_i), (_, bb_i)) when aa_i > bb_i ->
                        fold_leafs (E.expf_cons (scanned_op2exp op_aa_wl expAA expBB) op_bb_wl rest)
                    | ((SYN.InfixLeft, aa_i), (SYN.InfixLeft, bb_i)) when aa_i = bb_i ->
                        fold_leafs (E.expf_cons (scanned_op2exp op_aa_wl expAA expBB) op_bb_wl rest)
                    | ((_, aa_i), (_, bb_i)) when aa_i < bb_i ->
                        E.expf_cons expAA op_aa_wl (fold_leafs cdr)
                    | ((SYN.InfixRight, aa_i), (SYN.InfixRight, bb_i)) when aa_i = bb_i ->
                        E.expf_cons expAA op_aa_wl (fold_leafs cdr)
                    | _ ->
                        failwith (F.sprintf "Syntax error for operator priority. left fixity %s, right fixity %s"
                                    (SYN.fixity_str aa_fixity)
                                    (SYN.fixity_str bb_fixity))
              end
          | _ -> failwith "Arity 2 operator expression syntax error."
    in
      match fold_leafs list with
        | E.ExpF (exp, E.Op2End) -> exp
        | E.ExpF (exp, E.Op2F (_, E.Op2NoArg)) -> failwith "explist2term: section not implemented."
        | folded -> explist2term func folded
            (*
            (* TODO: The same form section scan function *)
              and explist2term_rsec func rs_list =
              match rs_list with
              E.Op2End -> exp10_fun exp
              | E.Op2F (op_aa, (E.ExpF (expBB, E.Op2End))) ->
              ...
            *)
  in
    { SYA.module_buffer = modbuf;
      SYA.op2_pat_n = patlist2term;
      SYA.op2_exp_0 = explist2term;
    }

let debug = true

let h_find_err err_fun =
  if debug then
    (fun ht k ->
       if H.mem ht k then
         H.find ht k
       else
         err_fun ())
  else H.find

let eval_sym_with_tab func_name tab sym =
  let err = (fun () -> failwith (F.sprintf "%s: %s not found." func_name (S.name sym))) in
    h_find_err err tab sym

let bind_value_to_tab tab sym value =
  H.add tab sym value

let eval_id_with_env env id =
  match ID.qual id with
    | ID.Q m ->
        (* let _ = F.printf "DEBUG: Qual %s\n" (S.name (ID.long_sym id)) in *)
        eval_sym_with_tab "eval_id: qual" (env_top_symtab env) (ID.long_sym id)
    | _ ->
        (* let _ = F.printf "DEBUG: Unqu %s\n" (S.name (ID.long_sym id)) in *)
        let short = (ID.short_sym id) in
        let lenv  = (env_symtab env) in
          eval_sym_with_tab "eval_id: unqual" lenv short


let simple_cons name = Cons (ID.qualid SYN.the_prelude_symbol (S.intern name), [])

let valTrue  = simple_cons "True"
let valFalse = simple_cons "False"

let prim_trace =
  let trace =
    try
      Sys.getenv "TRACE"
    with
        Not_found -> ""
  in
    match trace with
      | "" | "0" -> (fun _ -> ())
      | _        -> (fun s -> prerr_endline ("TRACE: " ^ s))

let bind_primitives env = 
  (* let table : (string, value_t) H.t = create_symtab () in *)
  let tab = env_top_symtab env in
  let raise_type_err name msg =
    failwith (F.sprintf "Primitive argument type error: %s: %s" name msg) in

  let mk_prim func arity = (fun () -> Closure (Prim (func), arity, [])) in
  let bind_prim name prim =
    let sym = S.intern name in
      (bind_value_to_tab tab sym prim,
       bind_value_to_tab tab (qualified_sym SYN.the_prelude_symbol sym) prim)
  in

  let _ =
    let cons = ":" in
      bind_prim cons
        (mk_prim
           (function
              | car :: cdr :: [] ->
                  Cons ((ID.qualid SYN.the_prelude_symbol (S.intern ":")),
                        [car; cdr])
              | _ -> raise_type_err cons "Argument count is not 2.")
         2)
  in

  let def_eager_num_op2 name i64f floatf =
    bind_prim name
      (mk_prim (function
                     thxx :: thyy :: [] ->
                       begin
                         match (thxx (), thyy ()) with
                             ((Literal x), (Literal y)) ->
                               begin
                                 match (x, y) with
                                     (SYN.Int (xi), SYN.Int (yi)) -> 
                                       prim_trace (F.sprintf "called '%s' with %s %s" name (Int64.to_string xi) (Int64.to_string yi));
                                       Literal (SYN.Int (i64f xi yi))
                                   | (SYN.Int (xi), SYN.Float (yf)) -> Literal (SYN.Float (floatf (Int64.to_float xi) yf))
                                   | (SYN.Float (xf), SYN.Int (yi)) -> Literal (SYN.Float (floatf xf (Int64.to_float yi)))
                                   | (SYN.Float (xf), SYN.Float (yf)) -> Literal (SYN.Float (floatf xf yf))
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
                                       (SYN.Int (xi), SYN.Int (yi)) ->
                                         prim_trace (F.sprintf "called '%s' with %s %s\n" name (Int64.to_string xi) (Int64.to_string yi));
                                         i64f xi yi
                                     | (SYN.Int (xi), SYN.Float (yf)) -> floatf (Int64.to_float xi) yf
                                     | (SYN.Float (xf), SYN.Int (yi)) -> floatf xf (Int64.to_float yi)
                                     | (SYN.Float (xf), SYN.Float (yf)) -> floatf xf yf
                                     | _ -> raise_type_err name "Non-number argument found."
                                 end
                               then valTrue else valFalse
                           | _ -> raise_type_err name "Non-literal arguemnt found."
                       end
                   | _ -> raise_type_err name "Argument count is not 2.") 2) in

  let _ = (def_eager_num_op2_bool "<=" (<=) (<=),
           def_eager_num_op2_bool ">=" (>=) (>=),
           def_eager_num_op2_bool "==" (=) (=),
           def_eager_num_op2_bool "/=" (<>) (<>)) in
                                       
  let prim_primError = "primError" in
  let _ = bind_prim prim_primError
    (mk_prim (function
                   th :: [] ->
                     begin
                       match th() with
                           Literal (SYN.String m) ->
                             failwith ("error: " ^ m)
                         | _ -> raise_type_err prim_primError "Non-literal arguemnt found."
                     end
                 | _ -> raise_type_err prim_primError "Arguemnt not found.") 1) in

  let prim_print = "print" in
  let _ = bind_prim prim_print
    (mk_prim (function
                   th :: [] ->
                     begin
                       match th() with
                           Literal (SYN.Int (i)) -> print_endline (Int64.to_string i); IO
                         | Literal (SYN.Float (f)) -> print_endline (string_of_float f); IO
                         (* | Literal (SYN.String (m)) -> print_endline m; IO *)
                         | Literal (SYN.String (_)) -> failwith "Not implemented: print: string argument."
                         | v -> raise_type_err prim_print ("Non-literal arguemnt found. " ^ (Std.dump v))
                     end
                 | _ -> raise_type_err prim_print "Arguemnt not found.") 1) in

  let prim_putStrLn = "putStrLn" in
  let _ = bind_prim prim_putStrLn
    (mk_prim (function
                   th :: [] ->
                     begin
                       match th() with
                         | Literal (SYN.String (m)) -> print_endline m; IO
                         | v -> raise_type_err prim_print ("Non-literal arguemnt found. " ^ (Std.dump v))
                     end
                 | _ -> raise_type_err prim_print "Arguemnt not found.") 1) in
    ()


let bind_thunk_to_env env id thunk =
  let symtab = env_symtab env in
  let _ = (match ID.qual id with
             | ID.Unq _ when env_top_symtab env == symtab ->
                 (* bind module top-level scope symbol's with qualified name *)
                 (* モジュールのトップレベルシンボルに束縛した値を修飾された名前にも束縛する *)
                 (* let _ = F.printf "DEBUG: bind(long) %s\n" (S.name (ID.long_sym id)) in *)
                 H.add symtab (ID.long_sym id) thunk
             | _ -> ())
  in
    (* let _ = F.printf "DEBUG: bind(short) %s\n" (S.name (ID.short_sym id)) in *)
  let _ = bind_value_to_tab symtab (ID.short_sym id) thunk in
    thunk

let module_top_tab program modsym =
  env_top_symtab (module_env (program_module_buffer program modsym))

let global_value program modsym sym =
  let top_tab = module_top_tab program modsym in
    eval_sym_with_tab "global_value" top_tab (qualified_sym modsym sym)

let bind_import_value env program is_qual modsym sym value =
  let top_tab = env_top_symtab env in
  let _ = if not is_qual then bind_value_to_tab top_tab sym value in 
    bind_value_to_tab top_tab (qualified_sym modsym sym) value

let mk_literal lit =
  Literal lit

let mk_lambda env pat_list exp where_env_fun =
  { arg_pat_list = pat_list;
    body = exp;
    lambda_env = env;
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

let applyClosureStack : value_t Stack.t = Stack.create ()

(* let dummy_eval_exp (env : env_t) (exp : E.t) =
  Bottom *)

(* let dummy_eval_func_exp (env : env_t) (fexp : E.fexp) =
  Bottom *)

(* let dummy_eval_arg_exp (env : env_t) (aexp : E.aexp) =
  Bottom *)

(* let eval_exp = dummy_eval_exp *)
(* let eval_func_exp = dummy_eval_func_exp *)
(* let eval_arg_exp = dummy_eval_arg_exp *)


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

(* TODO:
   delay_fun が thunk_t と同じ型なのは偶然である。
   取り違えに注意すべし。
   将来的に取り違えが無いように別の型になるように直すと良い。
*)

let make_thunk eval_fun env_fun evalee =
  let delay_fun = fun () -> (eval_fun (env_fun ()) evalee) in
  let thunk_ref = ref (Thunk delay_fun) in
    fun () -> expand_thunk thunk_ref

let rec make_arg_exp_thunk env_fun arg_exp =
  make_thunk eval_arg_exp env_fun arg_exp

and make_exp_thunk env_fun exp =
  make_thunk eval_exp env_fun exp

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
             let _ = bind_thunk_to_env env id thunk in (true, [thunk]))

      | P.AsP ((id, _), pat) ->
          (fun env thunk ->
             let (_, (matchp, tlist)) = (bind_thunk_to_env env id thunk,
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

      | P.LiteralP (literal, _) ->
          (fun _ thunk ->
             (match thunk () with
                  Literal expl when (SYN.eq_literal expl literal) -> true
                | _                                               -> false),
             [thunk])

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

      | P.MIntP (i64pat, _) ->
          (fun env thunk -> 
             (let value = thunk () in
                match value with
                  | Literal (SYN.Int i64val) when i64pat = (Int64.neg i64val)
                      -> true
                  | _ -> false),
             [thunk])

      | P.MFloatP (flpat, _) ->
          (fun env thunk -> 
             let value = thunk () in
               (match value with
                  | Literal (SYN.Float flval) when flpat = (-. flval) ->
                      true
                  | _ -> false),
             [thunk])

    | P.Irref pat ->
        failwith "pattern: Irref: Not implemented"
(*
        (fun env thunk -> bind_pat_with_thunk pat env thunk)
*)

    | P.ConOp2P ((id, _), pat1, pat2) ->
        (fun env thunk ->
           let value = thunk () in
             match value with
                 Cons (cid, args) when cid = id
                   -> sub_patterns_match env [pat1; pat2] args
               | _ -> (false, [thunk]))

    | P.Pat0 _ -> failwith ("Not converted Pat0 found. parser BUG!!")
    | P.Pat1 _ -> failwith ("Not converted Pat1 found. parser BUG!!")

    (* | _ -> failwith "pattern: Not implemented" *)

(* pattern_match : thunk を pattern にマッチ *)
and pattern_match lenv pat caller_env_fun evalee =
  bind_pat_with_thunk pat lenv (make_exp_thunk caller_env_fun evalee)
and pattern_match_arg_exp lenv pat caller_env_fun evalee =
  bind_pat_with_thunk pat lenv (make_arg_exp_thunk caller_env_fun evalee)

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
                            let loc_env = local_env lambda.lambda_env in
                              if (L.fold_left2
                                    (fun matchp pat arg_exp ->
                                       if matchp then let (matchp, _) = pattern_match_arg_exp loc_env pat (fun () -> caller_env) arg_exp in matchp
                                       else false)
                                    true
                                    lambda.arg_pat_list
                                    arg_exp_list)
                              then eval_exp (lambda.apply_where loc_env) lambda.body
                              else failwith "apply_closure: single pattern not match"

                        | MPat (lambda_list) ->
                            L.fold_left
                              (fun result lambda ->
                                 match result with
                                   | Bottom ->
                                       let loc_env = local_env lambda.lambda_env in
                                         if (L.fold_left2
                                               (fun matchp pat arg_exp ->
                                                  if matchp then let (matchp, _) = pattern_match_arg_exp loc_env pat (fun () -> caller_env) arg_exp in matchp
                                                  else false)
                                               true
                                               lambda.arg_pat_list
                                               arg_exp_list)
                                         then eval_exp (lambda.apply_where loc_env) lambda.body
                                         else failwith "apply_closure: all multi pattern not match"
                                   | result -> result)
                              Bottom
                              lambda_list

                        | Prim (prim_fun) ->
                            prim_fun (L.map (fun aexp -> (make_arg_exp_thunk (fun () -> caller_env) aexp)) arg_exp_list)
                    end
          end
            
    | x -> failwith (F.sprintf "apply_closure: Not closure value: %s" (Std.dump x))

(* eval_* : expression から thunk へ *)
and eval_arg_exp env =
  function
      E.VarE ((id, _)) ->
        begin
          (*
          if H.mem primTable (ID.name_str id) then
            H.find primTable (ID.name_str id)
          else
          *)
            (* let _ = print_endline (ID.name_str id) in *)
            let thunk = eval_id_with_env env id in
              thunk ()
        end

    | E.ConsE ((id, _)) ->
        (* let v = Cons (id, []) in v *)
        eval_id_with_env env id ()
         
    | E.LiteralE (lit, _) -> Literal lit

    | E.ParenE (exp) -> eval_exp env exp

    | E.TupleE (el) -> Tuple (L.map (fun e -> make_exp_thunk (fun () -> env) e) el)

    | E.ListE (el) -> List (L.map (fun e -> make_exp_thunk (fun () -> env) e) el)

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
    | E.FexpE (E.FfunE (E.LiteralE (lit, _))) ->
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
                  | Cons(id, []) when (ID.long_sym id) == SYN.bool_long_true  -> eval_exp env then_e
                  | Cons(id, []) when (ID.long_sym id) == SYN.bool_long_false -> eval_exp env else_e
                  | Cons(id, []) -> failwith (F.sprintf "exp: if: Type error %s" (S.name (ID.long_sym id)))
                  | x  -> failwith (F.sprintf "exp: if: Type error %s" (Std.dump x)))
           | E.CaseE (exp, []) ->
               Bottom
           | E.CaseE (exp, (CA.Simple (pat, case_exp, [])) :: alt_list) ->
               let loc_env = local_env env in
               let (match_p, tlist) = pattern_match loc_env pat (fun () -> env) exp in
                 if match_p then
                   eval_exp loc_env case_exp
                 else
                   eval_exp env (E.Top (E.CaseE (exp, alt_list), None))

           | x -> failwith (F.sprintf "exp: Not implemented: %s" (dump_exp x)))

and expand_rhs env rhs =
  let where_env lenv = function
    | None -> lenv
    | Some dl -> (decl_list_local_env lenv eval_decl dl) in
  let (ev_exp, new_local_env) =
    match rhs with
        D.Rhs (exp, where) -> (exp, (fun lenv -> where_env lenv where))
      | D.RhsWithGD (gdrhs_list, where) ->
          (L.fold_right
             (fun gdrhs else_e ->
                match gdrhs with
                    (GD.Guard gde, exp) ->
                      E.IfE (gde, exp, else_e))
             gdrhs_list
             (E.FexpE (E.FappE (E.FfunE (E.make_prelude_var_exp  "error"), E.LiteralE ((SYN.String "Unmatched pattern"), T.implicit_loc)))),
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
     (fun pat -> ignore (pattern_match env pat (fun () -> new_local_env env) ev_exp)))

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
          Some (sym, arity) -> let _ = bind_thunk_to_env env sym (make_thawed (Closure (MPat (L.rev revr), arity, []))) in ()
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


let eval_data_simple env typ = 
  function
    | C.App ((id, _), [])   ->
        let _ = bind_thunk_to_env env id (fun () -> (Cons (id, []))) in
          ()
    | C.App ((id, _), arity_ls)   ->
        ()
    | C.Op2 ((id, _), a1, a2)   ->
        ()
    | C.Label (_) -> ()

let (lastEvalDecl : E.t D.decl option ref) = ref None

let eval_topdecl env =
  function
    | D.Type (_) -> ()
    | D.Data (_, typ, cons_ls, _) ->
        let _ = L.map (fun cons -> eval_data_simple env typ cons) cons_ls in
          ()
    | D.NewType (_) -> ()
    | D.Class (_, _, _, cdecl_list) ->
        let _ = L.map (fun cd -> eval_cdecl env cd) cdecl_list in
          ()
    | D.Instance (_, _, _, idecl_list) ->
        let _ = L.map (fun instd -> eval_idecl env instd) idecl_list in
          ()
    | D.Default (_) -> ()
    | D.Decl d ->
        let _ = eval_decl env d in
          lastEvalDecl := Some d

let fixity_eval_gendecl env modbuf clsopt =
  function
    | D.TypeSig (_) -> ()
    | D.Fixity ((lnr, pri) as fixity, op_list) ->
        let _ =
          L.map
            (fun (op, _) ->
               bind_op2_fixity modbuf op (fixity, clsopt))
            op_list in
          ()
    | D.Empty -> ()
            
let fixity_eval_topdecl env modbuf =
  function
    | D.Type (_) -> ()
    | D.Data (_, typ, cons_ls, _) ->
        ()
    | D.NewType (_) -> ()
    | D.Class (_, _, (clsid, _), cdecl_list) ->
        let _ = L.map
          (fun cd ->
             match cd with
               | D.GenDeclC g -> fixity_eval_gendecl env modbuf (Some (ID.long_sym clsid)) g
               | _ -> ())
          cdecl_list in
          ()
    | D.Instance (_, _, _, idecl_list) ->
        ()
    | D.Default (_) -> ()
    | D.Decl (D.GenDecl g) -> fixity_eval_gendecl env modbuf None g
    | D.Decl (_) -> ()
        

let eval_export exbuf env =
  let (modex, ex) =
    (export_export_module exbuf,
     export_export exbuf) in
    function
      | M.EVar (id, _) ->
          H.add ex (ID.long_sym id) true
      | M.ECons ((id, _), M.List labels) ->
          H.add ex (ID.long_sym id) true
      | M.ECons ((id, _), M.All) ->
          H.add ex (ID.long_sym id) true
      | M.EClass ((id, _), M.List labels) ->
          H.add ex (ID.long_sym id) true
      | M.EClass ((id, _), M.All) ->
          H.add ex (ID.long_sym id) true
      | M.EMod (modsym, _) ->
          H.add modex modsym true

let fixity_eval_impdecl imp_map env =
  function
    | M.IDec (q, (modsym, _), Some (modas, _), impls) ->
        let mimp = (q, modsym, Some modas, impls) in
        let _ = (H.add imp_map modsym mimp, H.add imp_map modas mimp) in
          ()
    | M.IDec (q, (modsym, _), None, impls) ->
        H.add imp_map modsym (q, modsym, None, impls)
    | M.IEmpty -> ()

let fixity_eval_module exbuf modbuf =
  let env = module_env modbuf in
    match module_code modbuf with
        ((modsym, _), export_list, (import_list, topdecl_list)) ->
          let _ = L.map (eval_export exbuf env) export_list in
          let imp_map = module_import_module modbuf in
          let _ =
            if modsym == SYN.the_prelude_symbol then
              bind_op2_fixity modbuf ID.sp_colon ((SYN.InfixRight, 5), None)
            else
              (* import Prelude *)
              H.add imp_map SYN.the_prelude_symbol (M.NotQual, SYN.the_prelude_symbol, None, None)
          in
          let _ = L.map (fixity_eval_impdecl imp_map env) import_list in
          let _ = L.map (fixity_eval_topdecl env modbuf) topdecl_list in
            exbuf

let check_export exbuf modsym program =
  true

let check_export_module exbuf modsym program =
  (SaHt.mem program modsym) || (H.mem (export_export_module exbuf) modsym)

let resolve_import exbuf modbuf resolve_symbol resolve_module program =
  H.iter
    (fun name (qual, ex_mod_sym, as_sym_opt, impspec) ->
       let _ = (if not (check_export_module exbuf ex_mod_sym program) then
                  failwith (F.sprintf "Module '%s' not exported." (S.name ex_mod_sym)))
       in
       let is_qual =
         (match qual with
            | M.NotQual -> false
            | M.Qual    -> true)
       in
       let imp_mod_sym =
         (match as_sym_opt with
            | Some m -> m
            | None -> ex_mod_sym)
       in
       (* let env = module_env modbuf in *)
         match impspec with
           | Some (M.Imp  impls) ->
               let _ = L.map
                 (fun imp ->
                    (* resolve_import_symbol env imp_mod_sym ex_mod_sym is_qual program imp *)
                     resolve_symbol imp_mod_sym ex_mod_sym is_qual imp
                 )
                 impls
               in ()
           | Some (M.Hide impls) -> ()
           | None ->
               (* resolve_import_module env imp_mod_sym ex_mod_sym is_qual program *)
               resolve_module imp_mod_sym ex_mod_sym is_qual
                 (* (\* module import *\) () *)
    )
    (module_import_module modbuf)


let fixity_resolve_import_symbol ftab imp_mod_sym ex_mod_sym is_qual program =
  function
    | M.IVar ({ ID.qual = ID.Unq m; ID.short = ID.N sym }, _) ->
        bind_import_fixity
          ftab program is_qual imp_mod_sym sym
          (global_fixity program ex_mod_sym sym)
    | _ -> ()

let fixity_resolve_import_module ftab imp_mod_sym ex_mod_sym is_qual program =
  let ex_modbuf = program_module_buffer program ex_mod_sym in
  let ex_ftab = module_fixity ex_modbuf in
    H.iter
      (fun sym value ->
         match ID.parse_sym sym with
           | (None, sym) ->
               (* let _ = F.printf "DEBUG: fixity_import: imp %s ex %s sym %s\n"
                  (S.name imp_mod_sym) (S.name ex_mod_sym) (S.name sym) in *)
               bind_import_fixity
                 ftab program is_qual imp_mod_sym sym
                 value
           | (Some modsym, sym) -> ()
      )
      ex_ftab


let eval_module modbuf =
  let env = module_env modbuf in
    match module_code modbuf with
        ((modsym, _), export_list, (import_list, topdecl_list)) ->
          let _ =
            if modsym == SYN.the_prelude_symbol then
              bind_primitives (module_env modbuf)
          in
          let _ = L.map (eval_topdecl env) topdecl_list in
            ()

let resolve_import_symbol env imp_mod_sym ex_mod_sym is_qual program =
  function
    | M.IVar ({ ID.qual = ID.Unq m; ID.short = ID.N sym }, _) ->
        bind_import_value
          env program is_qual imp_mod_sym sym
          (global_value program ex_mod_sym sym)
    | _ -> ()

let resolve_import_module env imp_mod_sym ex_mod_sym is_qual program =
  let top_tab = module_top_tab program ex_mod_sym in
    H.iter
      (fun sym value ->
         match ID.parse_sym sym with
           | (None, sym) ->
               (* let _ = F.printf "DEBUG: import: mod %s imp %s ex %s sym %s\n"
                  (S.name imp_mod_sym) (S.name ex_mod_sym) (S.name sym) in *)
               bind_import_value
                 env program is_qual imp_mod_sym sym
                 value
           | (Some modsym, sym) -> ()
      )
      top_tab

let fixity_eval_program program =
  let exbuf =
    SaHt.fold
      (fun name modbuf exbuf ->
         fixity_eval_module exbuf modbuf)
      program
      (export_buffer ())
  in
  let () =
    SaHt.iter
      (fun name modbuf ->
         resolve_import
           exbuf modbuf
           (fun imp_mod_sym ex_mod_sym is_qual ->
              fixity_resolve_import_symbol (module_fixity modbuf) imp_mod_sym ex_mod_sym is_qual program)
           (fun imp_mod_sym ex_mod_sym is_qual ->
              fixity_resolve_import_module (module_fixity modbuf) imp_mod_sym ex_mod_sym is_qual program)
           program
      )
      program
  in
  let new_prog = SaHt.create
    S.name
    (fun _ -> "<mod>")
    (Some (fun x -> "Already loaded module: " ^ x))
    None (* (fun ks vs -> ks ^ " => " ^ vs) *)
    "<program buffer>"
  in
  let () =
    SaHt.iter
      (fun name modbuf ->
         SaHt.add new_prog
           name
           { modbuf with code = (SYA.maptree_module
                                   (list2term_func modbuf)
                                   (module_code modbuf)) })
      program
  in
    (exbuf, new_prog)

(* eval_program : 
   全ての module を thunk tree に変換した後で
   toplevel環境 main シンボルに束縛されている thunk を展開 *)
let eval_program (exbuf, program) =
  let () =
    SaHt.fold
      (fun name modbuf () ->
         eval_module modbuf)
      program
      ()
  in
  let _ =
    SaHt.iter
      (fun name modbuf ->
         let env = module_env modbuf in
           resolve_import
             exbuf modbuf
             (fun imp_mod_sym ex_mod_sym is_qual ->
                resolve_import_symbol env imp_mod_sym ex_mod_sym is_qual program)
             (fun imp_mod_sym ex_mod_sym is_qual ->
                resolve_import_module env imp_mod_sym ex_mod_sym is_qual program)
             program
      )
      program
  in
    (eval_id_with_env
       (module_env (program_module_buffer program SYN.the_main_symbol))
       (ID.qualid
          SYN.the_main_symbol
          SYN.the_entry_main_symbol)) ()

(*  *)
let eval_test fn =
  let prog = fixity_eval_program (load_program (LO.parse_files_with_prelude [fn])) in
    eval_program prog
