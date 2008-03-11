module F = Printf
module T = Token
module L = List

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

let prelude_name () = "Prelude"

let create_symtab () = Hashtbl.create 32

type 'a literal =
    Int of (int64 * 'a)
  | Float of (float * 'a)
  | Char of (char * 'a)
  | String of (string * 'a)

let unloc_literal  =
  function
      Int (i64, _) -> Int (i64, T.implicit_loc)
    | Float (f, _) -> Float (f, T.implicit_loc)
    | Char (c, _) -> Char (c, T.implicit_loc)
    | String (s, _) -> String (s, T.implicit_loc)

let must_be_int li err =
  match li with
      Int (i64, _) -> Int64.to_int i64
    | _ -> failwith err

module ModuleNamespace =
struct
  type module_name = string option ref

  let add n = ref (Some n)
  let add_local () = (ref None)

  let str n =
    match !n with
	Some n -> n
      | None -> "<local>"

end

module OnceAssoc =
struct
  module H = Hashtbl

  type ('a, 'b) t = {
(*     t : ('a, b) H.t; *)
(*     dup_err : string -> string; *)
    mem : ('a -> bool);
    find : ('a -> 'b);
    add : ('a -> 'b -> unit);
    replace : ('a -> 'b -> unit);

    iter : (('a -> 'b -> unit) -> unit);
    to_string : (unit -> string);
  }

  let create err_fun to_str_fun = 
    let tbl = create_symtab () in {
	mem = (fun k -> H.mem tbl k);
	find = (fun k -> H.find tbl k);
	add = (fun k v -> 
		 if H.mem tbl k then failwith (err_fun k)
		 else H.add tbl k v);
	replace = (fun k v -> 
		     H.replace tbl k v);

	iter = (fun f -> H.iter f tbl);
	to_string = (fun () -> H.fold (fun k v c -> c ^ (to_str_fun k v) ^ "\n") tbl "");
      }
    
end

module ParseBuffer =
struct
  module H = Hashtbl
  module OA = OnceAssoc
  module MN = ModuleNamespace

  type module_buffer = {
    mname : MN.module_name;
    op_fixity_assoc : (string, (fixity * tclass option)) OA.t;
    
    op_typesig_assoc : (string, tclass) OA.t;
    op_fun_assoc : (string, bool) OA.t;
    tclass_assoc : (string, tclass) OA.t;

    dump_buf : (unit -> string)
  }

  let mnstr mb = MN.str mb.mname

  let create_module mn = 
    let (fixity_a, typesig_a, fun_a, tclass_a) =
      (OA.create
	 ((^) "Multiple fixity declarations for ") 
	 (fun n (fix, tcls) -> n ^ (fixity_str fix)),
       OA.create
	 ((^) "Multiple declarations of ") 
	 (fun n tcls -> ((tclass_str tcls) ^ n)),
       OA.create
	 ((^) "Multiple declarations of ") 
	 (fun n _ -> "func(" ^ n ^ ")"),
       OA.create
	 ((^) "Multiple declarations of")
	 (fun n tcls -> ((tclass_str tcls) ^ n)))
    in {
	mname = mn;
	
	op_fixity_assoc = fixity_a;
	op_typesig_assoc = typesig_a;
	op_fun_assoc = fun_a;
	tclass_assoc = tclass_a;

	dump_buf = (fun () ->
		      (fixity_a.OA.to_string ()) ^ "\n" ^ (typesig_a.OA.to_string ()) ^ "\n" ^ (tclass_a.OA.to_string ()) ^ "\n")
      }


  type t = {
    module_assoc : (string, module_buffer) OA.t;

    get_module : (string -> module_buffer);
    get_local_module : (unit -> module_buffer);
  }

  let theBufferStack = Stack.create ()


  let create () = 
    let (massoc, lm) = (OA.create
			  (fun x -> "ParseBuffer BUG!: same name module added: " ^ x)
			  (fun k m -> m.dump_buf ()),
			create_module (MN.add_local ())) in
    let newb = {
      module_assoc  = massoc;

      get_module = (fun modid ->
		      if massoc.OA.mem modid then massoc.OA.find modid
		      else
			let m = create_module (MN.add modid) in
			let _ = massoc.OA.add modid m in m);
      get_local_module = (fun () -> lm);
    } in
      Stack.push newb theBufferStack;
      newb


  let last_buffer () =
    if Stack.is_empty theBufferStack then
      failwith "Parse buffer not initialized!"
    else
      Stack.top theBufferStack


  let find_module modid = (last_buffer ()).get_module modid
  let find_local_module () = (last_buffer ()).get_local_module ()

end

module Identifier =
struct

  module PBuf = ParseBuffer
  module MN = ModuleNamespace
  module OA = OnceAssoc

  type sp_con =
      Colon
    | Unit
    | NullList
    | Tuple of int

  type qualifier =
      Sp of sp_con
    | Qual of string option ref

  type 'loc id = {
    name : string;
    qual : qualifier;
    loc : 'loc;
  }

  let make_id_core n q loc = {
    name = n;
    qual = q;
    loc = loc
  }

  let make_local_id n loc = 
    make_id_core n (Qual (PBuf.find_local_module ()).PBuf.mname) loc

  let make_id modid n loc = 
    make_id_core n (Qual (PBuf.find_module modid).PBuf.mname) loc

  let sp_colon     loc = make_id_core ":" (Sp Colon) loc
  let sp_unit      loc = make_id_core "()" (Sp Unit) loc
  let sp_null_list loc = make_id_core "[]" (Sp NullList) loc
  let sp_tuple   i loc =
    make_id_core
      ("(" ^ (Array.fold_left (^) "" (Array.make (i-1) ",")) ^ ")")
      (Sp (Tuple i))
      loc

  let unloc id = { id with loc = T.implicit_loc }

  let make_id_with_mod data =
    let iwm = (fst data) in make_id iwm.T.modid iwm.T.id (snd data)

  let get_module_buffer id =
    match id.qual with
	Sp (_) -> PBuf.find_module (prelude_name ())
      | Qual nr ->
	  let lm = PBuf.find_local_module () in
	    if nr == lm.PBuf.mname then lm
	    else PBuf.find_module (MN.str nr)


  let as_op_set_fixity id fixity =
    (get_module_buffer id).PBuf.op_fixity_assoc.OA.add id.name fixity

  let as_op_set_typesig id tclass =
    (get_module_buffer id).PBuf.op_typesig_assoc.OA.add id.name tclass

  let class_regist id def =
    (get_module_buffer id).PBuf.tclass_assoc.OA.add id.name def
      
  let class_find id =
    (get_module_buffer id).PBuf.tclass_assoc.OA.find id.name
      
  let class_p id =
    (get_module_buffer id).PBuf.tclass_assoc.OA.mem id.name

  let fun_regist id def =
    (get_module_buffer id).PBuf.op_fun_assoc.OA.replace id.name def

  let fun_find id =
    (get_module_buffer id).PBuf.op_fun_assoc.OA.find id.name

  let op_prelude_def () =
    as_op_set_fixity (sp_colon T.implicit_loc) ((InfixRight, 5), None)

end

module ParsedData =
struct
  module H = Hashtbl
  module MN = ModuleNamespace
  module OA = OnceAssoc
  module PBuf = ParseBuffer
  module ID = Identifier

  let debugFlag = ref false
  let debug_out s =
    if !debugFlag then
      let _ = output_string stderr ("DEBUG: " ^ s ^ "\n") in
	flush stderr


  type op_def = {
    fname : string;
    fixity : fixity;
    tclass : tclass option
  }

  let op_def_string def =
    let fix_part d = d.fname ^ (fixity_str d.fixity) in
      (tclass_context_str def.tclass) ^ (fix_part def)

  let make_op_def pb_mod opn =
    let (fixity, fix_tclass) = 
      if pb_mod.PBuf.op_fixity_assoc.OA.mem opn then
	pb_mod.PBuf.op_fixity_assoc.OA.find opn
      else (default_op_fixity, None)
    in

    let sig_tclass = 
      if pb_mod.PBuf.op_typesig_assoc.OA.mem opn then
	Some (pb_mod.PBuf.op_typesig_assoc.OA.find opn)
      else None
    in

    let tclass =
      match (fix_tclass, sig_tclass) with
	  (None, None) -> None
	| (Some _, Some _) -> failwith ("Multiple declarations for " ^ (PBuf.mnstr pb_mod) ^ "." ^ opn)
	| (x, None) | (None, x) -> x
    in
      { fname = opn;
	fixity = fixity;
	tclass = tclass; }


  type module_data = {
    mname : string;
    op_assoc : (string, op_def) OA.t;
    tclass_assoc : (string, tclass) OA.t;
  }

  type 'module_e t = {
    module_assoc : (string, module_data) OA.t;
(*     prelude_mode : bool; *)
    local_module : module_data;

    syntax : 'module_e;
  }

  let module_to_string m =
    "module_data: " ^ m.mname ^ "\n" ^ (m.op_assoc.OA.to_string ())

  let convert_local_module pb_mod_local pb_mod local_module_name =
    let new_op_assoc = OA.create
      (fun _ -> "BUG: convert_local_module")
      (fun _ op_def -> op_def_string op_def)
    in

    let conv_op assoc =
      assoc.OA.iter
	(fun op _ ->
	   new_op_assoc.OA.replace
	     op
	     (make_op_def pb_mod op))
    in
    
    let _ = (conv_op pb_mod_local.PBuf.op_fixity_assoc,
	     conv_op pb_mod_local.PBuf.op_typesig_assoc,
	     conv_op pb_mod_local.PBuf.op_fun_assoc,
	     conv_op pb_mod.PBuf.op_fixity_assoc,
	     conv_op pb_mod.PBuf.op_typesig_assoc,
	     conv_op pb_mod.PBuf.op_fun_assoc) in
      (* only local module convert operator definition *)

      { mname = local_module_name;
	op_assoc = new_op_assoc;
	tclass_assoc = pb_mod.PBuf.tclass_assoc;
      }

  let convert_module pb_mod =
    { mname = PBuf.mnstr pb_mod;
      op_assoc = OA.create
	(fun _ -> "BUG: convert_module")
	(fun k v -> k ^ " => " ^ (op_def_string v));
      tclass_assoc = pb_mod.PBuf.tclass_assoc;
    }

  let get_module_data pd id =
    match id.ID.qual with
	ID.Sp (_) -> pd.module_assoc.OA.find (prelude_name ())
      | ID.Qual nr ->
	  let (mns, lm) = ((MN.str nr), pd.local_module) in
	    if mns = lm.mname then lm
	    else pd.module_assoc.OA.find mns
(*       failwith ("module " ^ modid ^" not found.") *)

  let id_op_def (pd, pre_pd) id =
    let (m, op) = (get_module_data pd id, id.ID.name) in
      if m.op_assoc.OA.mem op then
	m.op_assoc.OA.find op
      else
	let pm = pre_pd.module_assoc.OA.find (prelude_name ()) in
	  if pm.op_assoc.OA.mem op then
	    pm.op_assoc.OA.find op
	  else
	    failwith ("operator " ^ op ^" not found in module " ^ m.mname)

  let create_parsed_data pbuf ((local_module_id, _, _) as syntax_t) =
    let new_mod_assoc = OA.create
      (fun _ -> "BUG: convert_local_module")
      (fun k m -> module_to_string m)
    in
    let local_module_name = local_module_id.ID.name in
    let _ = pbuf.PBuf.module_assoc.OA.iter
      (fun modid pb_mod ->
	 if ((PBuf.mnstr pb_mod) <> local_module_name) then
	   let _ = debug_out ("Converting module '" ^ modid ^ "' ...") in
	   let mod_data = convert_module pb_mod in
	   let _ = debug_out ("Convert module done.") in
	     new_mod_assoc.OA.add mod_data.mname mod_data
	 else
	   debug_out ("Skipping module '" ^ modid ^ "' which is local")
(* 	   else convert_local_module (pbuf.PBuf.get_local_module ()) pb_mod local_module_name *)
      )
    in

    let _ = debug_out ("Converting local module '" ^ local_module_name ^ "' ...") in
    let lm = convert_local_module
      (pbuf.PBuf.get_local_module ())
      (pbuf.PBuf.get_module local_module_name)
      local_module_name
    in
    let _ = debug_out ("Convert local module done.") in

    let _ = new_mod_assoc.OA.add local_module_name lm in
    let _ = (pbuf.PBuf.get_local_module ()).PBuf.mname := Some local_module_name in
      { module_assoc = new_mod_assoc;

	local_module = lm;

	syntax = syntax_t
      }

end


module Module =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type symbols =
      List of T.loc ID.id list
    | All

  type import =
      IVar of T.loc ID.id
    | ICons of (T.loc ID.id * symbols)
    | IClass of (T.loc ID.id * symbols)

  type impspec =
      Imp of import list
    | Hide of import list

  type qual =
      NotQual
    | Qual

  type impdecl =
      IDec of (qual * T.loc ID.id * T.loc ID.id option * impspec option)
    | IEmpty

  type export =
      EVar of T.loc ID.id
    | ECons of (T.loc ID.id * symbols)
    | EClass of (T.loc ID.id * symbols)
    | EMod of T.loc ID.id

end

module Pattern =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type 'pat op2list_opf =
      Op2F of (T.loc ID.id * 'pat op2list_patf)
    | Op2End
  and 'pat op2list_patf =
      PatF of ('pat * 'pat op2list_opf)
    | Op2NoArg

  type pat =
      PlusP of (T.loc ID.id * int64 * T.loc)
    | VarP of T.loc ID.id
    | AsP of T.loc ID.id * pat
    | ConP of T.loc ID.id * pat list
    | LabelP of T.loc ID.id * (T.loc ID.id * pat) list
    | LiteralP of T.loc literal
    | WCardP
    | TupleP of pat list
    | ListP of pat list
    | MIntP of (int64 * T.loc)
    | MFloatP of (float * T.loc)
    | Irref of pat

    | Pat0 of pat op2list_patf
    | Pat1 of pat op2list_patf

    | ConOp2P of (T.loc ID.id * pat * pat)

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
    | Qtycon of T.loc ID.id

  type a_type =
      ConsAT of cons
    | VarAT of T.loc ID.id
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
      App of (T.loc ID.id * Type.arity list)
    | Op2 of (T.loc ID.id * Type.arity * Type.arity)
    | Label of (T.loc ID.id * (T.loc ID.id list * Type.arity) list)

  type newcon =
      Simple of (T.loc ID.id * Type.a_type)
    | WithFLD of (T.loc ID.id * T.loc ID.id * Type.typ)
end

module Context =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type clazz =
      Class of (T.loc ID.id * T.loc ID.id)
    | ClassApp of (T.loc ID.id * T.loc ID.id * Type.a_type list)

  type context = clazz list
end

module Instance =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type cons_arity =
      Type of (Type.cons * T.loc ID.id list)
    | Tuple of (T.loc ID.id list)
    | List of T.loc ID.id
    | Fun of (T.loc ID.id * T.loc ID.id)
end

module Decl =
struct
  module PBuf = ParseBuffer

  module PD = ParsedData
  module ID = Identifier
  module P = Pattern

  type mod_data = PD.module_data

  type gendecl =
      TypeSig of (T.loc ID.id list * Context.context option * Type.typ)
    | Fixity of (fixity * T.loc ID.id list)
    | Empty

  type 'exp decl =
      GenDecl of gendecl
    | FunDec of ('exp funlhs * 'exp rhs)
    | PatFunDec of (P.pat * 'exp rhs)

  and 'exp i =
      FunDecI of ('exp funlhs * 'exp rhs)
    | BindI of (T.loc ID.id * 'exp rhs)
    | EmptyI

  and 'exp c =
      GenDeclC of gendecl
    | FunDecC of ('exp funlhs * 'exp rhs)
    | BindC of (T.loc ID.id * 'exp rhs)

  and 'exp rhs =
      Rhs of ('exp * 'exp decl list option)
    | RhsWithGD of ('exp gdrhs * 'exp decl list option)

  and 'exp funlhs =
      FunDecLV of (T.loc ID.id * P.pat list)
    | Op2Pat of (T.loc ID.id * (P.pat * P.pat))
    | NestDec of ('exp funlhs * P.pat list)

  let op2lhs_op lhsd = fst lhsd
  let op2lhs_left lhsd = fst (snd lhsd)
  let op2lhs_right lhsd = snd (snd lhsd)

  let op2lhs lhsd =
    let op = op2lhs_op lhsd in
    let _ = ID.fun_regist op true in
      Op2Pat (op, (P.Pat1 (op2lhs_left lhsd), P.Pat1 (op2lhs_right lhsd)))

  type 'exp top =
      Type of (Type.typ * Type.typ)
    | Data of (Context.context * Type.typ * Constructor.con list * T.loc ID.id list)
    | NewType of (Context.context * Type.typ * Constructor.newcon * T.loc ID.id list)
    | Class of (Context.context * T.loc ID.id * T.loc ID.id * 'exp c list)
    | Instance of (Context.context * T.loc ID.id * Instance.cons_arity * 'exp i list)
    | Default of Type.typ list
    | Decl of 'exp decl

  let mk_class ctx name_id typev_id def =
    let _ = ID.class_regist name_id { cname = name_id.ID.name; type_var = typev_id.ID.name; ctxs = TClassCtx [] } in
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
  module P = Pattern
  module DS = DoStmt

  type mod_data = PD.module_data

  type 'exp op2list_opf =
      Op2F of (T.loc ID.id * 'exp op2list_expf)
    | Op2End
  and 'exp op2list_expf =
      ExpF of ('exp * 'exp op2list_opf)
(*     | UniOpF of (T.loc ID.id * 'exp * 'exp op2list_opf) *)
    | Op2NoArg

  type aexp =
      VarE of T.loc ID.id (* qvar *)
    | ConsE of T.loc ID.id (* gcon *)
    | LiteralE of T.loc literal
    | ParenE of t
    | TupleE of t list
    | ListE of t list
    | ASeqE of (t * t option * t option)
    | LCompE of (t * (t ListComp.qual) list)
    | MayLeftSecE of t op2list_expf
    | MayRightSecE of t op2list_opf
    | LeftSecE of (t * T.loc ID.id)
    | RightSecE of (T.loc ID.id * t)
    | LabelConsE of (T.loc ID.id * (T.loc ID.id * t) list)
    | LabelUpdE of (aexp * (T.loc ID.id * t) list)

  and fexp =
      FfunE of aexp
    | FappE of (fexp * aexp)
    | FappEID

  and t =
      FexpE of fexp
    | DoE of ((t DoStmt.stmt) list * t)
    | CaseE of (t * (t Case.alt) list)
    | IfE of (t * t * t)
    | LetE of (t Decl.decl list * t)
    | LambdaE of (Pattern.pat list * t)

    | Exp0 of (t op2list_expf)
    | Top of (t * (Type.typ * Context.context option) option)

    | Minus of (t)
    | VarOp2E of (T.loc ID.id * t * t)

  let make_fexp aexpl_lambda =
    let rec simplify =
      function
	  FappE (FappEID, x) -> FfunE x
	| FappE (fexp, aexp) -> FappE ((simplify fexp), aexp)
	| FfunE _ -> failwith "Already converted fexp(FfunE) found. parser BUG!!"
	| FappEID -> failwith "Already converted fexp(FappEID) found. parser BUG!!"
    in
      simplify (aexpl_lambda FappEID)


  let rec scan_pattern p =
    match p with
      P.PlusP (id, i64, _) ->
	(P.PlusP ((ID.unloc id), i64, T.implicit_loc),
	 ((fun a_id -> (ID.unloc a_id) <> id),
	  ()))
    | P.VarP (id) ->
	(P.VarP (ID.unloc id),
	 ((fun a_id -> (ID.unloc a_id) <> id),
	  ()))
    | P.AsP (id, pat) ->
	(P.AsP (ID.unloc id, to_pat_for_hash pat),
	 ((fun a_id ->
	     (ID.unloc a_id) <> id && fun_fv_p pat id),
	  ()))
    | P.ConP (id, pat_list) ->
	(P.ConP (ID.unloc id, L.map to_pat_for_hash pat_list),
	 ((fun a_id ->
	     (ID.unloc a_id) <> id && L.fold_left (fun b pat -> b && fun_fv_p pat a_id) true pat_list),
	  ()))
    | P.LabelP (id, fpat_list) ->
	(P.LabelP (ID.unloc id, L.map (fun (id, pat) -> (ID.unloc id, pat)) fpat_list),
	 ((fun a_id ->
	    (ID.unloc a_id) <> id && L.fold_left (fun b (fvar, pat) -> b && fun_fv_p pat a_id) true fpat_list),
	  ()))
    | P.LiteralP literal ->
	(P.LiteralP (unloc_literal literal),
	 ((fun _ -> true),
	  ()))
    | P.WCardP ->
	(P.WCardP,
	 ((fun _ -> true),
	  ()))
    | P.TupleP pat_list ->
	(P.TupleP (L.map to_pat_for_hash pat_list),
	 ((fun a_id -> L.fold_left (fun b pat -> b && fun_fv_p pat a_id) true pat_list),
	  ()))
    | P.ListP pat_list ->
	(P.ListP (L.map to_pat_for_hash pat_list),
	 ((fun a_id -> L.fold_left (fun b pat -> b && fun_fv_p pat a_id) true pat_list),
	  ()))
    | P.MIntP (int64, _) ->
	(P.MIntP (int64, T.implicit_loc),
	 ((fun _ -> true),
	  ()))
    | P.MFloatP (float, _) ->
	(P.MFloatP (float, T.implicit_loc),
	 ((fun _ -> true),
	  ()))
    | P.Irref pat ->
	(P.Irref (to_pat_for_hash pat),
	 (fun_fv_p pat,
	  ()))

(*     | P.Pat0 of pat op2list_patf *)
(*     | P.Pat1 of pat op2list_patf *)

    | P.ConOp2P (id, pat1, pat2) ->
	(P.ConOp2P (ID.unloc id, (to_pat_for_hash pat1), (to_pat_for_hash pat2)),
	 ((fun a_id -> fun_fv_p pat1 a_id && fun_fv_p pat2 a_id),
	  (fun exp ->  )))

    | _ -> failwith ("Not converted Pat0 or Pat1 found. parser BUG!!")

  and to_pat_for_hash p = fst (scan_pattern p)
  and fun_fv_p p = fst (snd (scan_pattern p))
(*   and match_p bind_fun p = (snd (snd (scan_pattern p))) bind_fun *)

end


module Scan =
struct
  module PBuf = ParseBuffer

  module PD = ParsedData
  module ID = Identifier
  module P = Pattern
  module D = Decl
  module DS = DoStmt
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
	  let _ = List.map (fun cdecl -> fixity_scan_cdecl (ID.class_find cls) cdecl) cdecl_list in
	    ()
      | _ -> ()

  let fixity_scan_module =
    function
	(_, _, (_, topdecl_list)) -> List.map fixity_scan_topdecl topdecl_list


  let rec scan_exp_top pdata =
      function
	  E.Top (E.Exp0 exp0, x) -> E.Top ((scan_op2exp pdata exp0), x)
	| _ -> failwith "Syntax BUG!!"

  and scan_op2exp pdata list =
    match list with
	E.ExpF (exp, E.Op2End) -> exp
      | E.ExpF (expAA, E.Op2F (op_aa, (E.ExpF (expBB, E.Op2End)))) ->
	  E.VarOp2E (op_aa, scan_exp10 pdata expAA, scan_exp10 pdata expBB)
      | E.ExpF (expAA, E.Op2F (op_aa, ((E.ExpF (expBB, E.Op2F (op_bb, rest))) as cdr))) ->
	  (let aa_fixity = (PD.id_op_def pdata op_aa).PD.fixity in
	   let bb_fixity = (PD.id_op_def pdata op_bb).PD.fixity in
	     match (aa_fixity, bb_fixity) with
	         ((_, aa_i), (_, bb_i)) when aa_i > bb_i ->
		   scan_op2exp pdata (E.ExpF (E.VarOp2E (op_aa, expAA, expBB), E.Op2F (op_bb, rest)))
	       | ((InfixLeft, aa_i), (InfixLeft, bb_i)) when aa_i = bb_i ->
		   scan_op2exp pdata (E.ExpF (E.VarOp2E (op_aa, expAA, expBB), E.Op2F (op_bb, rest)))
	       | ((_, aa_i), (_, bb_i)) when aa_i < bb_i ->
		   E.VarOp2E (op_aa, scan_exp10 pdata expAA, (scan_op2exp pdata cdr))
	       | ((InfixRight, aa_i), (InfixRight, bb_i)) when aa_i = bb_i ->
		   E.VarOp2E (op_aa, scan_exp10 pdata expAA, (scan_op2exp pdata cdr))
	       | _ ->
		   failwith (Printf.sprintf "Syntax error for operation priority. left fixity %s, right fixity %s"
			       (fixity_str aa_fixity)
			       (fixity_str bb_fixity)))
      | _ -> failwith "Arity 2 operator expression syntax error."

  and scan_exp10 pdata exp10 =
    match exp10 with
	E.LambdaE (x, exp) -> E.LambdaE (x, scan_exp_top pdata exp)
      | E.LetE (x, exp) -> E.LetE (x, scan_exp_top pdata exp)
      | E.IfE (pred, t, f) -> E.IfE (scan_exp_top pdata pred, scan_exp_top pdata t, scan_exp_top pdata f)
      | E.CaseE (exp, x) -> E.CaseE (scan_exp_top pdata exp, x)
      | E.DoE (stmt_list, exp) -> E.DoE (List.map (scan_do_stmt pdata) stmt_list, scan_exp_top pdata exp)
      | fexp -> fexp

  and scan_do_stmt pdata stmt =
    match stmt with
	DS.Exp (exp) -> DS.Exp (scan_exp_top pdata exp)
      | DS.Cons (pat, exp) -> DS.Cons (pat, scan_exp_top pdata exp)
      | DS.Let (dlist) -> DS.Let (List.map (op2_scan_decl pdata) dlist)
      | DS.Empty -> DS.Empty


  and op2_scan_fundec pdata =
    function
	D.Op2Pat (varop, (P.Pat1 pat1a, P.Pat1 pat1b)) ->
	  D.Op2Pat (varop, (P.scan_op2pat 1 pdata pat1a, P.scan_op2pat 1 pdata pat1b))
      | x -> x

  and op2_scan_rhs pdata =
      function
	  D.Rhs (exp, None) -> D.Rhs (scan_exp_top pdata exp, None)
	| D.Rhs (exp, Some exp_decl_list) -> D.Rhs (scan_exp_top pdata exp, Some (List.map (op2_scan_decl pdata) exp_decl_list))
	| x -> x

  and op2_scan_decl pdata =
    function
	D.FunDec (lhs, rhs) -> D.FunDec ((op2_scan_fundec pdata lhs), (op2_scan_rhs pdata rhs))
      | D.PatFunDec (P.Pat0 pat, rhs) -> D.PatFunDec ((P.scan_op2pat 0 pdata pat), (op2_scan_rhs pdata rhs))
      | x -> x

  and op2_scan_cdecl pdata tcls =
    function
	D.FunDecC (lhs, rhs) -> D.FunDecC ((op2_scan_fundec pdata lhs), (op2_scan_rhs pdata rhs))
      | x -> x

  and op2_scan_topdecl pdata =
    function 
	D.Decl d -> D.Decl (op2_scan_decl pdata d)
      | D.Class (ctx, cls, x, cdecl_list) ->
	  let new_cdecl_list = List.map (fun cdecl -> op2_scan_cdecl pdata (ID.class_find cls) cdecl) cdecl_list in
	    D.Class (ctx, cls, x, new_cdecl_list)
      | x -> x

  and op2_scan_module pdata =
    function
	(x, y, (z, topdecl_list)) -> (x, y, (z, List.map (op2_scan_topdecl pdata) topdecl_list))
    
end
