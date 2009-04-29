
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

(* シンボルテーブル *)
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

