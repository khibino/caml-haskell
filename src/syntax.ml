module F = Printf
module T = Token


type fixity_lnr =
    Infix
  | InfixLeft
  | InfixRight
      
let fixity_lnr_string =
  function
      Infix -> "n"
    | InfixLeft -> "l"
    | InfixRight -> "r"

type fixity = (fixity_lnr * int)

let default_op_fixity = (InfixLeft, 9)

let fixity_str fix =
  Printf.sprintf "(%s,%d)" (fixity_lnr_string (fst fix)) (snd fix)

type tclass = {
  cname : string;
  type_var : string;
  ctxs : context_list;
}

and context_list =
    TClassCtx of (tclass list)

let tclass_str tc =
  (Printf.sprintf "(%s %s) => " tc.cname tc.type_var)

let tclass_context_str =
  function
      None -> ""
    | Some tc -> tclass_str tc

let prelude_module () = "Prelude"

let create_symtab () = Hashtbl.create 32

type 'a literal =
    Int of (int64 * 'a)
  | Float of (float * 'a)
  | Char of (char * 'a)
  | String of (string * 'a)


let must_be_int li err =
  match li with
      Int (i64, _) -> Int64.to_int i64
    | _ -> failwith err

module ParseBuffer =
struct
  type module_buffer = {
    mname : string;
    op_fixity_assoc : (string, (fixity * tclass option)) Hashtbl.t;
    op_typesig_assoc : (string, tclass) Hashtbl.t;
(*     op_fun_assoc : (string, ) Hashtbl.t; *)
    tclass_assoc : (string, tclass) Hashtbl.t;
  }

  let fixity_assoc_dump fm =
    Hashtbl.iter (fun n (fix, tco) -> print_endline (n ^ (fixity_str fix))) fm

  let typesig_assoc_dump tm =
    Hashtbl.iter (fun n tcls -> print_endline ((tclass_str tcls) ^ n)) tm

  type t = {
    module_assoc : (string, module_buffer) Hashtbl.t;
    prelude_mode : bool;
    mutable local_module : string;
  }

  let add_module_with_buffer pbuf modid =
    let m = { mname = modid;
	      op_fixity_assoc = create_symtab ();
	      op_typesig_assoc = create_symtab ();
	      tclass_assoc = create_symtab (); } in
    let _ = Hashtbl.add pbuf.module_assoc m.mname m in
      m

  let find_module_with_buffer pbuf modid =
    if Hashtbl.mem pbuf.module_assoc modid then
      Hashtbl.find pbuf.module_assoc modid
    else
      add_module_with_buffer pbuf modid

  let theLastBuffer = ref None

  let create_with_prelude_flag prelude_p =
    let newb = {
      module_assoc = create_symtab ();
      prelude_mode = prelude_p;
      local_module = if prelude_p then prelude_module () else "<local>"
    } in
    let _ = add_module_with_buffer newb newb.local_module in
      theLastBuffer := Some newb;
      newb

  let create () = create_with_prelude_flag false

  let last_buffer () = match !theLastBuffer with
      None -> failwith "Parse buffer not initialized!"
    | Some x -> x

  let local_module_name () = (last_buffer ()).local_module


  let add_module modid = add_module_with_buffer (last_buffer ()) modid

  let find_module modid = find_module_with_buffer (last_buffer ()) modid

  let op_with_assoc modid op assoc_fun fails_fun =
    let m = assoc_fun (find_module modid) in
    let defined = Hashtbl.mem m op in
      (defined,
       ((fun () -> Hashtbl.find m op),
	(fun v ->
	   if defined then failwith (fails_fun op)
	   else Hashtbl.add m op v)))

  let op_with_fixity_assoc modid op =
    op_with_assoc
      modid op
      (fun modb -> modb.op_fixity_assoc)
      ((^) "Multiple fixity declarations for ")
    
  let op_with_typesig_assoc modid op =
    op_with_assoc
      modid op
      (fun modb -> modb.op_typesig_assoc)
      ((^) "Multiple declarations for ")

  let dump_module m =
    fixity_assoc_dump m.op_fixity_assoc;
    typesig_assoc_dump m.op_typesig_assoc

  let class_regist modid conid def =
    Hashtbl.add (find_module modid).tclass_assoc conid def
      
  let class_find modid conid =
    Hashtbl.find (find_module modid).tclass_assoc conid
      
  let class_p modid conid =
    Hashtbl.mem (find_module modid).tclass_assoc conid

end

module Identifier =
struct
  module PB = ParseBuffer

  type op_attr =
      Op2
    | Fun
      
  type sp_con =
      Colon
    | Unit
    | NullList
    | Tuple of int

  type 'module_info qualifier =
      NotQ
(*     | Global *)
    | Local
    | Qual of string * 'module_info option

  type ('module_info, 'loc) id =
      SpCon of (sp_con * 'loc)
    | Cons of ('module_info qualifier * op_attr * string * 'loc)
    | Var  of ('module_info qualifier * op_attr * string * 'loc)

  let make_cons op q n l = Cons (q, op, n, l)
  let make_var op q n l = Var (q, op, n, l)

  let make_id_with_mod mkid_fun op data =
    let iwm = (fst data) in mkid_fun op (Qual (iwm.T.modid, None)) iwm.T.id (snd data)

  let make_cons_with_mod op data =
    make_id_with_mod make_cons op data

  let make_var_with_mod op data =
    make_id_with_mod make_var op data

  let to_qual id =
    match id with
	SpCon (_) -> id
      | Cons (NotQ, op, n, l) -> Cons (Local, op, n, l)
      | Var  (NotQ, op, n, l) -> Var  (Local, op, n, l)
      | _ -> failwith "Syntax BUG!"

  let name_with_local_module id local_module =
    match id with
	SpCon (Colon, _) ->    (prelude_module (), ":")
      |	SpCon (Unit, _) ->     (prelude_module (), "()")
      |	SpCon (NullList, _) -> (prelude_module (), "[]")
      |	SpCon (Tuple i, _) ->  (prelude_module (), "(" ^ (Array.fold_left (^) "" (Array.make (i-1) ",")) ^ ")")
      | Cons ((NotQ | Local), op, n, l) -> (local_module, n)
      | Var  ((NotQ | Local), op, n, l) -> (local_module, n)
      | Cons (Qual (modn, _), op, n, l) -> (modn, n)
      | Var  (Qual (modn, _), op, n, l) -> (modn, n)

  let name id =
    name_with_local_module id (PB.local_module_name ())

  let op_with_fixity_assoc id =
    let (modid, op) = name id in
      PB.op_with_fixity_assoc modid op

  let op_with_typesig_assoc id =
    let (modid, op) = name id in
      PB.op_with_typesig_assoc modid op

  let as_op_set_fixity id fixity =
    (snd (snd (op_with_fixity_assoc id))) fixity

  let as_op_set_typesig id tclass =
    (snd (snd (op_with_typesig_assoc id))) tclass

  let op_prelude_def () =
    if (PB.last_buffer ()).PB.prelude_mode then
      as_op_set_fixity (SpCon (Colon, T.implicit_loc)) ((InfixRight, 5), None)
    
end

module ParsedData =
struct
  module PBuf = ParseBuffer
  module ID = Identifier 

  type op_def = {
    fname : string;
    fixity : fixity;
    tclass : tclass option
  }

  let op_def_string def =
    let fix_part d = d.fname ^ (fixity_str d.fixity) in
      (tclass_context_str def.tclass) ^ (fix_part def)

  let make_op_def modid op =
    let (fixity, fix_tclass) = 
      let (defined, (getter, _)) = PBuf.op_with_fixity_assoc modid op in
	(if defined then getter ()
	 else (default_op_fixity, None))
    in

    let sig_tclass = 
      let (defined, (getter, _)) = PBuf.op_with_typesig_assoc modid op in
	(if defined then Some (getter ())
	 else None)
    in
    let tclass =
      match (fix_tclass, sig_tclass) with
	  (None, None) -> None
	| (Some _, Some _) -> failwith ("Multiple declarations for " ^ modid ^ "." ^ op)
	| (x, None) | (None, x) -> x
    in
      { fname = op;
	fixity = fixity;
	tclass = tclass; }

  let op_assoc_dump oa =
    Hashtbl.iter (fun fn def -> print_endline (op_def_string def)) oa

  type module_data = {
    mname : string;
    op_assoc : (string, op_def) Hashtbl.t;
    tclass_assoc : (string, tclass) Hashtbl.t;
  }

  type 'module_e t = {
    module_assoc : (string, module_data) Hashtbl.t;
    prelude_mode : bool;
    local_module : module_data;

    syntax : 'module_e;
  }

  let dump_module m =
    op_assoc_dump m.op_assoc

  let convert_local_module pb_mod local_module_name =
    let new_op_assoc = create_symtab () in
    let _ =
      Hashtbl.iter
	(fun op _ ->
	   Hashtbl.add
	     new_op_assoc
	     op
	     (make_op_def pb_mod.PBuf.mname op))
	pb_mod.PBuf.op_typesig_assoc in

    let _ =
      Hashtbl.iter
	(fun op _ ->
	   Hashtbl.add (* quick hack. duplicated value may be added against same key *)
	     new_op_assoc
	     op
	     (make_op_def pb_mod.PBuf.mname op))
	pb_mod.PBuf.op_fixity_assoc in 

      (* only local module convert operator definition *)

      { mname = local_module_name;
	op_assoc = new_op_assoc;
	tclass_assoc = pb_mod.PBuf.tclass_assoc;
      }

  let convert_module pb_mod =
    { mname = pb_mod.PBuf.mname;
      op_assoc = create_symtab ();
      tclass_assoc = pb_mod.PBuf.tclass_assoc;
    }

  let get_module_data pd modid =
    if Hashtbl.mem pd.module_assoc modid then
      Hashtbl.find pd.module_assoc modid
    else
      failwith ("module " ^ modid ^" not found.")
    

  let id_op_def (pd, pre_pd) id =
    let (modid, op) = ID.name_with_local_module id pd.local_module.mname in
    let m = get_module_data pd modid in
      if Hashtbl.mem m.op_assoc op then
	Hashtbl.find m.op_assoc op
      else
	let pm = get_module_data pre_pd (prelude_module ()) in
	  if Hashtbl.mem pm.op_assoc op then
	    Hashtbl.find pm.op_assoc op
	  else
	    failwith ("operator " ^ op ^" not found in module " ^ modid)

end


module Module =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type symbols =
      List of (mod_data, T.loc) ID.id list
    | All

  type import =
      IVar of (mod_data, T.loc) ID.id
    | ICons of ((mod_data, T.loc) ID.id * symbols)
    | IClass of ((mod_data, T.loc) ID.id * symbols)

  type impspec =
      Imp of import list
    | Hide of import list

  type qual =
      NotQual
    | Qual

  type impdecl =
      IDec of (qual * (mod_data, T.loc) ID.id * (mod_data, T.loc) ID.id option * impspec option)
    | IEmpty

  type export =
      EVar of (mod_data, T.loc) ID.id
    | ECons of ((mod_data, T.loc) ID.id * symbols)
    | EClass of ((mod_data, T.loc) ID.id * symbols)
    | EMod of (mod_data, T.loc) ID.id

end

module Pattern =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type 'pat op2list_opf =
      Op2F of ((mod_data, T.loc) ID.id * 'pat op2list_patf)
    | Op2End
  and 'pat op2list_patf =
      PatF of ('pat * 'pat op2list_opf)
    | Op2NoArg

  type pat =
      PlusP of ((mod_data, T.loc) ID.id * int64 * T.loc)
    | VarP of (mod_data, T.loc) ID.id
    | AsP of (mod_data, T.loc) ID.id * pat
    | ConP of (mod_data, T.loc) ID.id * pat list
    | LabelP of (mod_data, T.loc) ID.id * ((mod_data, T.loc) ID.id * pat) list
    | LiteralP of T.loc literal
    | WCardP
    | TupleP of pat list
    | ListP of pat list
    | MIntP of (int64 * T.loc)
    | MFloatP of (float * T.loc)
    | Irref of pat

    | Pat0 of pat op2list_patf
    | Pat1 of pat op2list_patf

    | ConOp2P of ((mod_data, T.loc) ID.id * pat * pat)

(*
pati  	 ->  	 pati+1 [qconop(n,i) pati+1]
	| 	lpati
	| 	rpati
lpati 	-> 	(lpati | pati+1) qconop(l,i) pati+1
rpati 	-> 	pati+1 qconop(r,i) (rpati | pati+1)
*)

  let rec scan_op2pat min_i pdata list =
    match list with
	PatF (pat, Op2End) -> pat
      | PatF (patAA, Op2F (op_aa, (PatF (patBB, Op2End)))) ->
	  ConOp2P (op_aa, patAA, patBB)
      | PatF (patAA, Op2F (op_aa, ((PatF (patBB, Op2F (op_bb, rest))) as cdr))) ->
	  (let aa_fixity = (PD.id_op_def pdata op_aa).PD.fixity in
	   let bb_fixity = (PD.id_op_def pdata op_bb).PD.fixity in
	     match (aa_fixity, bb_fixity) with
		 ((_, aa_i), _) when aa_i < min_i ->
		   failwith (Printf.sprintf "Pat%d cannot involve fixity %s operator." min_i (fixity_str aa_fixity))
	       | (_, (_, bb_i)) when bb_i < min_i ->
		   failwith (Printf.sprintf "Pat%d cannot involve fixity %s operator." min_i (fixity_str bb_fixity))
	       | ((_, aa_i), (_, bb_i)) when aa_i > bb_i ->
		   scan_op2pat min_i pdata (PatF (ConOp2P (op_aa, patAA, patBB), Op2F (op_bb, rest)))
	       | ((InfixLeft, aa_i), (InfixLeft, bb_i)) when aa_i = bb_i ->
		   scan_op2pat min_i pdata (PatF (ConOp2P (op_aa, patAA, patBB), Op2F (op_bb, rest)))
	       | ((_, aa_i), (_, bb_i)) when aa_i < bb_i ->
		   ConOp2P (op_aa, patAA, (scan_op2pat min_i pdata cdr))
	       | ((InfixRight, aa_i), (InfixRight, bb_i)) when aa_i = bb_i ->
		   ConOp2P (op_aa, patAA, (scan_op2pat min_i pdata cdr))
	       | _ ->
		   failwith (Printf.sprintf "Syntax error for operation priority. left fixity %s, right fixity %s"
			       (fixity_str aa_fixity)
			       (fixity_str bb_fixity)))
      | _ -> failwith "Arity 2 operator pattern syntax error."

end

module Guard =
struct
  type 'exp t =
      Guard of 'exp
end

type 'exp gdrhs = ('exp Guard.t * 'exp) list

module Type =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type cons =
      TupleC of int
    | FunC
    | ListC
    | UnitC
    | Qtycon of (mod_data, T.loc) ID.id

  type a_type =
      ConsAT of cons
    | VarAT of (mod_data, T.loc) ID.id
    | TupleAT of typ list
    | ListAT of typ
    | AT of typ

  and b_type =
      AppBT of (b_type * a_type)
    | BT of a_type

  and typ =
      FunT of (b_type * typ)
    | TT of b_type

  let simple_btype tycon_id =
    BT (ConsAT (Qtycon tycon_id))

  type arity =
      Lazy of typ
    | Strict of a_type

end

module Constructor =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type con =
      App of ((mod_data, T.loc) ID.id * Type.arity list)
    | Op2 of ((mod_data, T.loc) ID.id * Type.arity * Type.arity)
    | Label of ((mod_data, T.loc) ID.id * ((mod_data, T.loc) ID.id list * Type.arity) list)

  type newcon =
      Simple of ((mod_data, T.loc) ID.id * Type.a_type)
    | WithFLD of ((mod_data, T.loc) ID.id * (mod_data, T.loc) ID.id * Type.typ)
end

module Context =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type clazz =
      Class of ((mod_data, T.loc) ID.id * (mod_data, T.loc) ID.id)
    | ClassApp of ((mod_data, T.loc) ID.id * (mod_data, T.loc) ID.id * Type.a_type list)

  type context = clazz list
end

module Instance =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type cons_arity =
      Type of (Type.cons * (mod_data, T.loc) ID.id list)
    | Tuple of ((mod_data, T.loc) ID.id list)
    | List of (mod_data, T.loc) ID.id
    | Fun of ((mod_data, T.loc) ID.id * (mod_data, T.loc) ID.id)
end

module Decl =
struct
  module PBuf = ParseBuffer

  module PD = ParsedData
  module ID = Identifier
  module P = Pattern

  type mod_data = PD.module_data

  type gendecl =
      TypeSig of ((mod_data, T.loc) ID.id list * Context.context option * Type.typ)
    | Fixity of (fixity * (mod_data, T.loc) ID.id list)
    | Empty

  type 'exp decl =
      GenDecl of gendecl
    | FunDec of ('exp funlhs * 'exp rhs)
    | PatFunDec of (P.pat * 'exp rhs)

  and 'exp i =
      FunDecI of ('exp funlhs * 'exp rhs)
    | BindI of ((mod_data, T.loc) ID.id * 'exp rhs)
    | EmptyI

  and 'exp c =
      GenDeclC of gendecl
    | FunDecC of ('exp funlhs * 'exp rhs)
    | BindC of ((mod_data, T.loc) ID.id * 'exp rhs)

  and 'exp rhs =
      Rhs of ('exp * 'exp decl list option)
    | RhsWithGD of ('exp gdrhs * 'exp decl list option)

  and 'exp funlhs =
      FunDecLV of ((mod_data, T.loc) ID.id * P.pat list)
    | Op2Pat of ((mod_data, T.loc) ID.id * (P.pat * P.pat))
    | NestDec of ('exp funlhs * P.pat list)

  let op2lhs_op lhsd = fst lhsd
  let op2lhs_left lhsd = fst (snd lhsd)
  let op2lhs_right lhsd = snd (snd lhsd)

  let op2lhs lhsd =
    Op2Pat (op2lhs_op lhsd, (P.Pat1 (op2lhs_left lhsd), P.Pat1 (op2lhs_right lhsd)))

  type 'exp top =
      Type of (Type.typ * Type.typ)
    | Data of (Context.context * Type.typ * Constructor.con list * (mod_data, T.loc) ID.id list)
    | NewType of (Context.context * Type.typ * Constructor.newcon * (mod_data, T.loc) ID.id list)
    | Class of (Context.context * (mod_data, T.loc) ID.id * (mod_data, T.loc) ID.id * 'exp c list)
    | Instance of (Context.context * (mod_data, T.loc) ID.id * Instance.cons_arity * 'exp i list)
    | Default of Type.typ list
    | Decl of 'exp decl

  let mk_class ctx name_id typev_id def =
    let (modn, id) = ID.name name_id in
    let (typv_modn, typev) = ID.name typev_id in
    let _ = PBuf.class_regist modn id { cname = id; type_var = typev; ctxs = TClassCtx [] } in
      Class (ctx, name_id, typev_id, def)

end

module ListComp =
struct
  type 'exp qual =
      Gen of (Pattern.pat * 'exp)
    | Let of 'exp Decl.decl list
    | Guard of 'exp
end

module Case =
struct
  type 'exp alt =
      Simple of (Pattern.pat * 'exp * 'exp Decl.decl list)
    | WithGD of (Pattern.pat * ('exp Guard.t * 'exp) list * 'exp Decl.decl list)
    | Empty
end

module DoStmt =
struct
  type 'exp stmt =
      Exp of 'exp
    | Cons of (Pattern.pat * 'exp)
    | Let of 'exp Decl.decl list
    | Empty
end

module Expression =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type 'exp op2list_opf =
      Op2F of ((mod_data, T.loc) ID.id * 'exp op2list_expf)
    | Op2End
  and 'exp op2list_expf =
      ExpF of ('exp * 'exp op2list_opf)
(*     | UniOpF of ((mod_data, T.loc) ID.id * 'exp * 'exp op2list_opf) *)
    | Op2NoArg

  type aexp =
      VarE of (mod_data, T.loc) ID.id (* qvar *)
    | ConsE of (mod_data, T.loc) ID.id (* gcon *)
    | LiteralE of T.loc literal
    | ParenE of t
    | TupleE of t list
    | ListE of t list
    | ASeqE of (t * t option * t option)
    | LCompE of (t * (t ListComp.qual) list)
    | MayLeftSecE of t op2list_expf
    | MayRightSecE of t op2list_opf
    | LeftSecE of (t * (mod_data, T.loc) ID.id)
    | RightSecE of ((mod_data, T.loc) ID.id * t)
    | LabelConsE of ((mod_data, T.loc) ID.id * ((mod_data, T.loc) ID.id * t) list)
    | LabelUpdE of (aexp * ((mod_data, T.loc) ID.id * t) list)

  and t =
      FappE of aexp list
    | DoE of ((t DoStmt.stmt) list * t)
    | CaseE of (t * (t Case.alt) list)
    | IfE of (t * t * t)
    | LetE of (t Decl.decl list * t)
    | LambdaE of (Pattern.pat list * t)

    | Exp0 of (t op2list_expf)
    | Top of (t * (Type.typ * Context.context option) option)

    | Minus of (t)
    | VarOp2E of ((mod_data, T.loc) ID.id * t * t)


  let rec scan_op2exp pdata list =
    match list with
	ExpF (exp, Op2End) -> exp
      | ExpF (expAA, Op2F (op_aa, (ExpF (expBB, Op2End)))) ->
	  VarOp2E (op_aa, expAA, expBB)
      | ExpF (expAA, Op2F (op_aa, ((ExpF (expBB, Op2F (op_bb, rest))) as cdr))) ->
	  (let aa_fixity = (PD.id_op_def pdata op_aa).PD.fixity in
	   let bb_fixity = (PD.id_op_def pdata op_bb).PD.fixity in
	     match (aa_fixity, bb_fixity) with
	         ((_, aa_i), (_, bb_i)) when aa_i > bb_i ->
		   scan_op2exp pdata (ExpF (VarOp2E (op_aa, expAA, expBB), Op2F (op_bb, rest)))
	       | ((InfixLeft, aa_i), (InfixLeft, bb_i)) when aa_i = bb_i ->
		   scan_op2exp pdata (ExpF (VarOp2E (op_aa, expAA, expBB), Op2F (op_bb, rest)))
	       | ((_, aa_i), (_, bb_i)) when aa_i < bb_i ->
		   VarOp2E (op_aa, expAA, (scan_op2exp pdata cdr))
	       | ((InfixRight, aa_i), (InfixRight, bb_i)) when aa_i = bb_i ->
		   VarOp2E (op_aa, expAA, (scan_op2exp pdata cdr))
	       | _ ->
		   failwith (Printf.sprintf "Syntax error for operation priority. left fixity %s, right fixity %s"
			       (fixity_str aa_fixity)
			       (fixity_str bb_fixity)))
      | _ -> failwith "Arity 2 operator expression syntax error."

end


module Scan =
struct
  module PBuf = ParseBuffer

  module PD = ParsedData
  module ID = Identifier
  module P = Pattern
  module D = Decl
  module E = Expression

  let fixity_scan_gendecl =
    function
	(D.Fixity (fix, id_list), tcls) ->
	  let _ = List.map (fun id -> ID.as_op_set_fixity id (fix, tcls)) id_list in ()
      | (D.TypeSig (id_list, _, _), None) ->
	  ()
      | (D.TypeSig (id_list, _, _), Some tcls) ->
	  let _ = List.map (fun id -> ID.as_op_set_typesig id tcls) id_list in ()
      | _ -> ()

  let fixity_scan_decl =
    function
	D.GenDecl g -> fixity_scan_gendecl (g, None)
      | _ -> ()

  let fixity_scan_cdecl tcls =
    function
	D.GenDeclC g -> fixity_scan_gendecl (g, (Some tcls))
      | _ -> ()
	  
  let fixity_scan_topdecl =
    function 
	D.Decl d -> fixity_scan_decl d
      | D.Class (ctx, cls, _, cdecl_list) ->
	  let (modid, cname) = ID.name cls in
	  let _ = List.map (fun cdecl -> fixity_scan_cdecl (PBuf.class_find modid cname) cdecl) cdecl_list in
	    ()
      | _ -> ()

  let fixity_scan_module =
    function
	(_, _, (_, topdecl_list)) -> List.map fixity_scan_topdecl topdecl_list



  let op2_scan_fundec pdata =
    function
	D.Op2Pat (varop, (P.Pat1 pat1a, P.Pat1 pat1b)) ->
	  D.Op2Pat (varop, (P.scan_op2pat 1 pdata pat1a, P.scan_op2pat 1 pdata pat1b))
      | x -> x


  let op2_scan_exp pdata =
      function
	  E.Top (E.Exp0 exp0, x) -> E.Top ((E.scan_op2exp pdata exp0), x)
	| _ -> failwith "Syntax BUG!!"

  let rec op2_scan_rhs pdata =
      function
	  D.Rhs (exp, None) -> D.Rhs (op2_scan_exp pdata exp, None)
	| D.Rhs (exp, Some exp_decl_list) -> D.Rhs (op2_scan_exp pdata exp, Some (List.map (op2_scan_decl pdata) exp_decl_list))
	| x -> x

  and op2_scan_decl pdata =
    function
	D.FunDec (lhs, rhs) -> D.FunDec ((op2_scan_fundec pdata lhs), (op2_scan_rhs pdata rhs))
      | D.PatFunDec (P.Pat0 pat, rhs) -> D.PatFunDec ((P.scan_op2pat 0 pdata pat), (op2_scan_rhs pdata rhs))
      | x -> x

  let op2_scan_cdecl pdata tcls =
    function
	D.FunDecC (lhs, rhs) -> D.FunDecC ((op2_scan_fundec pdata lhs), (op2_scan_rhs pdata rhs))
      | x -> x

  let op2_scan_topdecl pdata =
    function 
	D.Decl d -> D.Decl (op2_scan_decl pdata d)
      | D.Class (ctx, cls, x, cdecl_list) ->
	  let (modid, cname) = ID.name cls in
	  let new_cdecl_list = List.map (fun cdecl -> op2_scan_cdecl pdata (PBuf.class_find modid cname) cdecl) cdecl_list in
	    D.Class (ctx, cls, x, new_cdecl_list)
      | x -> x

  let op2_scan_module pdata =
    function
	(x, y, (z, topdecl_list)) -> (x, y, (z, List.map (op2_scan_topdecl pdata) topdecl_list))
    
end

module PBuf = ParseBuffer
module PD = ParsedData
module ID = Identifier
module H = Hashtbl
module D = Decl

let go_prelude_mode () =
  print_endline "--- Go to Prelude load mode ---";
  let pbuf = PBuf.create_with_prelude_flag true in
  let _ = ID.op_prelude_def () in
    pbuf

let create_parsed_data pbuf ((local_module_id, _, _) as syntax_t) =
  let (_, local_module_name) = ID.name local_module_id in
  print_endline (Printf.sprintf "creating PD from %s buffer and %s syntax" pbuf.PBuf.local_module local_module_name);
  let new_mod_assoc = create_symtab () in
  let _ = H.iter
    (fun modid pb_mod ->
       print_endline ("converting " ^ modid);
       let mod_data =
	 if (pb_mod.PBuf.mname <> pbuf.PBuf.local_module) then PD.convert_module pb_mod
	 else PD.convert_local_module pb_mod local_module_name
       in
	 H.add new_mod_assoc mod_data.PD.mname mod_data)
    pbuf.PBuf.module_assoc
  in
    { PD.module_assoc = new_mod_assoc;
      PD.prelude_mode = pbuf.PBuf.prelude_mode;
      PD.local_module =
	if H.mem new_mod_assoc local_module_name then
	  H.find new_mod_assoc local_module_name
	else
	  failwith ("BUG: Cannot find module " ^ local_module_name)
      ;
      PD.syntax = syntax_t
    }
