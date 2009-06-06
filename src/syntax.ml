module F = Printf
module T = Token
module L = List
module OH = OrderedHash

type ('k, 'v) ordh = ('k, 'v) OH.t

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

let eq_literal aa bb =
  (unloc_literal aa) = (unloc_literal bb)

let must_be_int li err =
  match li with
      Int (i64, _) -> Int64.to_int i64
    | _ -> failwith err

module ModuleNamespace =
struct
  type t = string option ref

  let add n = ref (Some n)
  let add_local () = (ref None)

  let str n =
    match !n with
        Some n -> n
      | None -> failwith "ModuleNamespace.str called with not named local module!"  (* "<local>" *)

end

module ParseBuffer =
struct
  module H = Hashtbl
  module OA = OnceAssoc
  module MN = ModuleNamespace

  type module_buffer = {
    mns : MN.t;
    op_fixity_assoc : (string, (fixity * tclass option)) OA.t;
    
    op_typesig_assoc : (string, tclass) OA.t;
    op_fun_assoc : (string, bool) OA.t;
    tclass_assoc : (string, tclass) OA.t;

    dump_buf : (unit -> string)
  }

  let mnstr mb = MN.str mb.mns

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
        mns = mn;
        
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

(*
  type 'loc id = {
    name : string;
    qual : qualifier;
    loc : 'loc;
  }

  type idwl = T.loc id
*)

  type id = {
    name : string;
    qual : qualifier;
  }

  type idwl = (id * T.loc)

  let make_id_core n q = {
    name = n;
    qual = q;
  }

  let make_local_id n = 
    make_id_core n (Qual (PBuf.find_local_module ()).PBuf.mns)

  let make_id modid n = 
    make_id_core n (Qual (PBuf.find_module modid).PBuf.mns)

  let idwl id loc = (id, loc)

  let make_local_idwl n loc = idwl (make_local_id n) loc

  let idwul id = idwl id T.implicit_loc

  let sp_colon     = make_id_core ":" (Sp Colon)
  let sp_unit      = make_id_core "()" (Sp Unit)
  let sp_null_list = make_id_core "[]" (Sp NullList)
  let sp_tuple   i =
    make_id_core
      ("(" ^ (Array.fold_left (^) "" (Array.make (i-1) ",")) ^ ")")
      (Sp (Tuple i))

  let unloc idwl = fst idwl
  let eq_idwl aa bb = (unloc aa) = (unloc bb)

  let name_str id =
    match id.qual with
        Sp _ -> id.name
      | Qual { contents = Some qname } -> qname ^ "." ^ id.name
      | Qual { contents = None }       -> "<undef>." ^ id.name

  let make_id_with_mod iwm = make_id iwm.T.modid iwm.T.id

  let make_idwl_with_mod (iwm, loc) = idwl (make_id_with_mod iwm) loc

  let get_module_buffer id =
    match id.qual with
        Sp (_) -> PBuf.find_module (prelude_name ())
      | Qual nr ->
          let lm = PBuf.find_local_module () in
            if nr == lm.PBuf.mns then lm
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
    as_op_set_fixity sp_colon ((InfixRight, 5), None)

end

(* ParseBuffer.module_buffer --> ParsedData.module_data *)
module ParsedData =
struct
  module H = Hashtbl
  module MN = ModuleNamespace
  module OA = OnceAssoc
  module PBuf = ParseBuffer
  module ID = Identifier

  let debugFlag = ref false  (* Syntax.ParsedData.debugFlag := true *)
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
    let v = { fname = opn;
              fixity = fixity;
              tclass = tclass; } in
      debug_out (Printf.sprintf "op '%s' defined." (op_def_string v));
      v


  type module_data = {
    mname : string;
    mn_ref : MN.t;
    op_assoc : (string, op_def) OA.t;
    tclass_assoc : (string, tclass) OA.t;
  }

  type 'module_e t = {
    module_assoc : (string, module_data) OA.t;
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

    let conv_op a_pb =
      let conv_op_assoc assoc =
        assoc.OA.iter
          (fun op _ ->
             new_op_assoc.OA.replace
               op
               (make_op_def pb_mod_local op))
      in
        (conv_op_assoc a_pb.PBuf.op_fixity_assoc,
         conv_op_assoc a_pb.PBuf.op_typesig_assoc,
         conv_op_assoc a_pb.PBuf.op_fun_assoc)
    in
    
    let _ = (conv_op pb_mod_local, conv_op pb_mod) in
      (* only local module convert operator definition *)

      { mname = local_module_name;
        mn_ref = pb_mod_local.PBuf.mns;
        op_assoc = new_op_assoc;
        tclass_assoc = pb_mod.PBuf.tclass_assoc;
      }

  let convert_module pb_mod =
    { mname = PBuf.mnstr pb_mod;
      mn_ref = pb_mod.PBuf.mns;
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

  let create_parsed_data pbuf (((local_module_id, _), _, _) as syntax_t) =
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
(*         else convert_local_module (pbuf.PBuf.get_local_module ()) pb_mod local_module_name *)
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
    let _ = (pbuf.PBuf.get_local_module ()).PBuf.mns := Some local_module_name in
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
      List of ID.idwl list
    | All

  type import =
      IVar of ID.idwl
    | ICons of (ID.idwl * symbols)
    | IClass of (ID.idwl * symbols)

  type impspec =
      Imp of import list
    | Hide of import list

  type qual =
      NotQual
    | Qual

  type impdecl =
      IDec of (qual * ID.idwl * ID.idwl option * impspec option)
    | IEmpty

  type export =
      EVar of ID.idwl
    | ECons of (ID.idwl * symbols)
    | EClass of (ID.idwl * symbols)
    | EMod of ID.idwl

end

module Pattern =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type 'pat op2list_opf =
      Op2F of (ID.idwl * 'pat op2list_patf)
    | Op2End
  and 'pat op2list_patf =
      PatF of ('pat * 'pat op2list_opf)
    | Op2NoArg

  type pat =
      PlusP of (ID.idwl * int64 * T.loc)
    | VarP of ID.idwl
    | AsP of ID.idwl * pat
    | ConP of ID.idwl * pat list
    | LabelP of ID.idwl * (ID.idwl * pat) list
    | LiteralP of T.loc literal
    | WCardP
    | TupleP of pat list
    | ListP of pat list
    | MIntP of (int64 * T.loc)
    | MFloatP of (float * T.loc)
    | Irref of pat

    | Pat0 of pat op2list_patf
    | Pat1 of pat op2list_patf

    | ConOp2P of (ID.idwl * pat * pat)

(*
pati     ->      pati+1 [qconop(n,i) pati+1]
        |       lpati
        |       rpati
lpati   ->      (lpati | pati+1) qconop(l,i) pati+1
rpati   ->      pati+1 qconop(r,i) (rpati | pati+1)
*)

  let rec scan_op2pat min_i pdata pat_fun list =
    match list with
        PatF (pat, Op2End) -> pat_fun pat
      | PatF (patAA, Op2F (op_aa_wl, (PatF (patBB, Op2End)))) ->
          ConOp2P (op_aa_wl, pat_fun patAA, pat_fun patBB)
      | PatF (patAA, Op2F ((op_aa, _) as op_aa_wl, ((PatF (patBB, Op2F ((op_bb, _) as op_bb_wl, rest))) as cdr))) ->
          (let aa_fixity = (PD.id_op_def pdata op_aa).PD.fixity in
           let bb_fixity = (PD.id_op_def pdata op_bb).PD.fixity in
             match (aa_fixity, bb_fixity) with
                 ((_, aa_i), _) when aa_i < min_i ->
                   failwith (Printf.sprintf "Pat%d cannot involve fixity %s operator." min_i (fixity_str aa_fixity))
               | (_, (_, bb_i)) when bb_i < min_i ->
                   failwith (Printf.sprintf "Pat%d cannot involve fixity %s operator." min_i (fixity_str bb_fixity))
               | ((_, aa_i), (_, bb_i)) when aa_i > bb_i ->
                   scan_op2pat min_i pdata pat_fun (PatF (ConOp2P (op_aa_wl, pat_fun patAA, pat_fun patBB), Op2F (op_bb_wl, rest)))
               | ((InfixLeft, aa_i), (InfixLeft, bb_i)) when aa_i = bb_i ->
                   scan_op2pat min_i pdata pat_fun (PatF (ConOp2P (op_aa_wl, pat_fun patAA, pat_fun patBB), Op2F (op_bb_wl, rest)))
               | ((_, aa_i), (_, bb_i)) when aa_i < bb_i ->
                   ConOp2P (op_aa_wl, pat_fun patAA, (scan_op2pat min_i pdata pat_fun cdr))
               | ((InfixRight, aa_i), (InfixRight, bb_i)) when aa_i = bb_i ->
                   ConOp2P (op_aa_wl, pat_fun patAA, (scan_op2pat min_i pdata pat_fun cdr))
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
    | Qtycon of ID.idwl

  type a_type =
      ConsAT of cons
    | VarAT of ID.idwl
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
      App of (ID.idwl * Type.arity list)
    | Op2 of (ID.idwl * Type.arity * Type.arity)
    | Label of (ID.idwl * (ID.idwl list * Type.arity) list)

  type newcon =
      Simple of (ID.idwl * Type.a_type)
    | WithFLD of (ID.idwl * ID.idwl * Type.typ)
end

module Context =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type clazz =
      Class of (ID.idwl * ID.idwl)
    | ClassApp of (ID.idwl * ID.idwl * Type.a_type list)

  type context = clazz list
end

module Instance =
struct
  module PD = ParsedData
  module ID = Identifier 

  type mod_data = PD.module_data

  type cons_arity =
      Type of (Type.cons * ID.idwl list)
    | Tuple of (ID.idwl list)
    | List of ID.idwl
    | Fun of (ID.idwl * ID.idwl)
end

module Decl =
struct
  module PBuf = ParseBuffer

  module PD = ParsedData
  module ID = Identifier
  module P = Pattern

  type mod_data = PD.module_data

  type gendecl =
      TypeSig of (ID.idwl list * Context.context option * Type.typ)
    | Fixity of (fixity * ID.idwl list)
    | Empty

  type 'exp decl =
      GenDecl of gendecl
    | FunDec of (('exp funlhs * 'exp rhs) list)
    | PatBind of (P.pat * 'exp rhs)

  (* Instance *)
  and 'exp i =
      FunDecI of (('exp funlhs * 'exp rhs) list)
    | BindI of (ID.idwl * 'exp rhs)
    | EmptyI

  (* Class *)
  and 'exp c =
      GenDeclC of gendecl
    | FunDecC of (('exp funlhs * 'exp rhs) list)
    | BindC of (ID.idwl * 'exp rhs)

  and 'exp rhs =
      Rhs of ('exp * 'exp decl list option)
    | RhsWithGD of ('exp gdrhs * 'exp decl list option)

  and 'exp funlhs =
      FunLV of (ID.idwl * P.pat list)
    | Op2Fun of (ID.idwl * (P.pat * P.pat))
    | NestDec of ('exp funlhs * P.pat list)

  let op2lhs_op lhsd = fst lhsd
  let op2lhs_left lhsd = fst (snd lhsd)
  let op2lhs_right lhsd = snd (snd lhsd)

  let op2lhs lhsd =
    let (op, _) as op_wl = op2lhs_op lhsd in
    let _ = ID.fun_regist op true in
      Op2Fun (op_wl, (P.Pat1 (op2lhs_left lhsd), P.Pat1 (op2lhs_right lhsd)))

  type 'exp top =
      Type of (Type.typ * Type.typ)
    | Data of (Context.context * Type.typ * Constructor.con list * ID.idwl list)
    | NewType of (Context.context * Type.typ * Constructor.newcon * ID.idwl list)
    | Class of (Context.context * ID.idwl * ID.idwl * 'exp c list)
    | Instance of (Context.context * ID.idwl * Instance.cons_arity * 'exp i list)
    | Default of Type.typ list
    | Decl of 'exp decl

  let mk_class ctx ((name_id, _) as name_id_wl) ((typev_id, _) as typev_id_wl) def =
    let _ = ID.class_regist name_id { cname = name_id.ID.name; type_var = typev_id.ID.name; ctxs = TClassCtx [] } in
      Class (ctx, name_id_wl, typev_id_wl, def)

  let defpair_from_topdecl =
    function
        Decl (FunDec (dp :: _)) -> Some dp
      | _ -> None

  let topdecl_cons decl pre_decl =
    match (decl, pre_decl) with
        (Decl (FunDec [defpair]), Decl (FunDec pre_decl_list)) -> Decl (FunDec (defpair :: pre_decl_list))
      | _ -> assert false

  let defpair_from_decl =
    function
        FunDec (dp :: _) -> Some dp
      | _ -> None

  let decl_cons decl pre_decl =
    match (decl, pre_decl) with
        (FunDec [defpair], FunDec pre_decl_list) -> FunDec (defpair :: pre_decl_list)
      | _ -> assert false

  let defpair_from_i =
    function
        FunDecI (dp :: _) -> Some dp
      | _ -> None

  let i_cons decl pre_decl =
    match (decl, pre_decl) with
        (FunDecI [defpair], FunDecI pre_decl_list) -> FunDecI (defpair :: pre_decl_list)
      | _ -> assert false

  let defpair_from_c =
    function
        FunDecC (dp :: _) -> Some dp
      | _ -> None

  let c_cons decl pre_decl =
    match (decl, pre_decl) with
        (FunDecC [defpair], FunDecC pre_decl_list) -> FunDecC (defpair :: pre_decl_list)
      | _ -> assert false

  let poly_fundec_cons ndecl decl_list get_defpair merge =
    match decl_list with
        [] -> [ndecl]
      | pre_decl :: tail ->
          begin
            match ((get_defpair ndecl), (get_defpair pre_decl)) with
                (Some (FunLV ((id, _), _), _), Some (FunLV ((car_id, _), _), _))
                  when id = car_id
                    -> (merge ndecl pre_decl) :: tail
              | _   -> ndecl :: decl_list
          end

(*
  let fundec_cons 
*)

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
  module A = Array

  type mod_data = PD.module_data

  type 'exp op2list_opf =
      Op2F of (ID.idwl * 'exp op2list_expf)
    | Op2End
  and 'exp op2list_expf =
      ExpF of ('exp * 'exp op2list_opf)
(*     | UniOpF of (ID.idwl * 'exp * 'exp op2list_opf) *)
    | Op2NoArg

  type aexp =
      VarE of ID.idwl (* qvar *)
    | ConsE of ID.idwl (* gcon *)
    | LiteralE of T.loc literal
    | ParenE of t
    | TupleE of t list
    | ListE of t list
    | ASeqE of (t * t option * t option)
    | LCompE of (t * (t ListComp.qual) list)

    | MayLeftSecE of t op2list_expf
    | MayRightSecE of t op2list_opf

    | LeftSecE of (t * ID.idwl)
    | RightSecE of (ID.idwl * t)

    | LabelConsE of (ID.idwl * (ID.idwl, t) ordh)
    | LabelUpdE of (aexp * (ID.idwl, t) ordh)

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
    | VarOp2E of (ID.idwl * t * t)

  let make_fexp aexpl_lambda =
    let rec simplify =
      function
          FappE (FappEID, x) -> FfunE x
        | FappE (fexp, aexp) -> FappE ((simplify fexp), aexp)
        | FfunE _ -> failwith "Already converted fexp(FfunE) found. parser BUG!!"

        | FappEID -> failwith "Already converted fexp(FappEID) found. parser BUG!!"
    in
      simplify (aexpl_lambda FappEID)

  let make_aexp_exp aexp = FexpE (FfunE aexp)

  let cons_aexp_list cons_fexp =
    let rec cons_aexp_list exp arg_list =
      match exp with
          FfunE (ConsE id) -> Some (id, (A.of_list arg_list))
        | FappE (exp, a)   -> cons_aexp_list exp (a :: arg_list)
        | _                -> None
    in cons_aexp_list cons_fexp []

  let make_var_exp name pd =
    VarE (ID.idwul (ID.make_id_core name (ID.Qual pd.PD.mn_ref)))

end


module Scan =
struct
  module L = List

  module PBuf = ParseBuffer

  module PD = ParsedData
  module ID = Identifier
  module P = Pattern
  module GD = Guard
  module D = Decl
  module DS = DoStmt
  module E = Expression

  let fixity_scan_gendecl =
    function
        (D.Fixity (fix, id_list), tcls) ->
          let _ = List.map (fun (id, _) -> ID.as_op_set_fixity id (fix, tcls)) id_list in ()
      | (D.TypeSig (id_list, _, _), None) ->
          ()
      | (D.TypeSig (id_list, _, _), Some tcls) ->
          let _ = List.map (fun (id, _) -> ID.as_op_set_typesig id tcls) id_list in ()
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
      | D.Class (ctx, (cls, _), _, cdecl_list) ->
          let _ = List.map (fun cdecl -> fixity_scan_cdecl (ID.class_find cls) cdecl) cdecl_list in
            ()
      | _ -> ()

  let fixity_scan_module =
    function
        (_, _, (_, topdecl_list)) -> List.map fixity_scan_topdecl topdecl_list



  let lastScanBug = ref None

  let rec scan_exp_top pdata =
      function
          E.Top (exp, x) -> E.Top ((scan_exp0 pdata exp), x)
        | x -> lastScanBug := Some x; failwith "Syntax BUG!!"

  and scan_exp0 pdata =
    function
        E.Exp0 exp0 -> (scan_op2exp pdata exp0)
      | x -> x

  and scan_op2exp pdata list =
    match list with
        E.ExpF (exp, E.Op2End) -> scan_exp10 pdata exp
      | E.ExpF (expAA, E.Op2F (op_aa, (E.ExpF (expBB, E.Op2End)))) ->
          E.VarOp2E (op_aa, scan_exp10 pdata expAA, scan_exp10 pdata expBB)
      | E.ExpF (expAA, E.Op2F ((op_aa, _) as op_aa_wl, ((E.ExpF (expBB, E.Op2F ((op_bb, _) as op_bb_wl, rest))) as cdr))) ->
          (let aa_fixity = (PD.id_op_def pdata op_aa).PD.fixity in
           let bb_fixity = (PD.id_op_def pdata op_bb).PD.fixity in
             (* Printf.printf "(%s, %d) vs (%s, %d)\n" op_aa.ID.name (snd aa_fixity) op_bb.ID.name (snd bb_fixity); *)
             match (aa_fixity, bb_fixity) with
                 ((_, aa_i), (_, bb_i)) when aa_i > bb_i ->
                   scan_op2exp pdata (E.ExpF (E.VarOp2E (op_aa_wl, expAA, expBB), E.Op2F (op_bb_wl, rest)))
               | ((InfixLeft, aa_i), (InfixLeft, bb_i)) when aa_i = bb_i ->
                   scan_op2exp pdata (E.ExpF (E.VarOp2E (op_aa_wl, expAA, expBB), E.Op2F (op_bb_wl, rest)))
               | ((_, aa_i), (_, bb_i)) when aa_i < bb_i ->
                   E.VarOp2E (op_aa_wl, scan_exp10 pdata expAA, (scan_op2exp pdata cdr))
               | ((InfixRight, aa_i), (InfixRight, bb_i)) when aa_i = bb_i ->
                   E.VarOp2E (op_aa_wl, scan_exp10 pdata expAA, (scan_op2exp pdata cdr))
               | _ ->
                   failwith (Printf.sprintf "Syntax error for operation priority. left fixity %s, right fixity %s"
                               (fixity_str aa_fixity)
                               (fixity_str bb_fixity)))
      | _ -> failwith "Arity 2 operator expression syntax error."

  and scan_atom_exp pdata =
    function
        E.ParenE exp -> E.ParenE (scan_exp_top pdata exp)
      | E.TupleE elist -> E.TupleE (L.map (fun exp -> scan_exp_top pdata exp) elist)
      | E.ListE elist -> E.ListE (L.map (fun exp -> scan_exp_top pdata exp) elist)
      | x -> x

  and scan_fun_exp pdata =
    function
        E.FfunE aexp -> E.FfunE (scan_atom_exp pdata aexp)
      | E.FappE (fexp, aexp) -> E.FappE (scan_fun_exp pdata fexp, scan_atom_exp pdata aexp)
      | E.FappEID -> failwith "Syntax BUG!!. FappEID found."

  and scan_exp10 pdata exp10 =
    match exp10 with
        E.LambdaE (x, exp) -> E.LambdaE (x, scan_exp_top pdata exp)
      | E.LetE (decl_list, exp) -> E.LetE (L.map (op2_scan_decl pdata) decl_list, scan_exp_top pdata exp)
      | E.IfE (pred, t, f) -> E.IfE (scan_exp_top pdata pred, scan_exp_top pdata t, scan_exp_top pdata f)
      | E.CaseE (exp, x) -> E.CaseE (scan_exp_top pdata exp, x)
      | E.DoE (stmt_list, exp) -> E.DoE (L.map (scan_do_stmt pdata) stmt_list, scan_exp_top pdata exp)
      | E.FexpE fexp -> E.FexpE (scan_fun_exp pdata fexp)
      | x -> x

  and scan_do_stmt pdata stmt =
    match stmt with
        DS.Exp (exp) -> DS.Exp (scan_exp_top pdata exp)
      | DS.Cons (pat, exp) -> DS.Cons (op2_scan_pat pdata pat, scan_exp_top pdata exp)
      | DS.Let (dlist) -> DS.Let (List.map (op2_scan_decl pdata) dlist)
      | DS.Empty -> DS.Empty

  and op2_scan_pat pdata =
    function
        P.Pat0 (patf) -> P.scan_op2pat 0 pdata (op2_scan_pat pdata) patf
      | P.Pat1 (patf) -> P.scan_op2pat 1 pdata (op2_scan_pat pdata) patf
      | p -> op2_scan_atompat pdata p

  and op2_scan_atompat pdata =
    function
        P.AsP (id, p) -> P.AsP (id, op2_scan_pat pdata p)
      | P.ConP (id, plist) -> P.ConP (id, L.map (fun p0 -> op2_scan_pat pdata p0) plist)
      | P.LabelP (id, idp_list) -> P.LabelP (id, (L.map (fun (id, p0) -> (id, op2_scan_pat pdata p0)) idp_list))
      | P.TupleP (plist) -> P.TupleP (L.map (fun p0 -> op2_scan_pat pdata p0) plist)
      | P.ListP  (plist) -> P.ListP  (L.map (fun p0 -> op2_scan_pat pdata p0) plist)
      | P.Irref (p) -> P.Irref (op2_scan_pat pdata p)
      | x -> x

  and op2_scan_funlhs pdata =
    function
        D.Op2Fun (varop, (pat_aa, pat_bb)) ->
          D.Op2Fun (varop, (op2_scan_pat pdata pat_aa, op2_scan_pat pdata pat_bb))
      | D.NestDec (lhs, pat_list) ->
          D.NestDec (op2_scan_funlhs pdata lhs, L.map (fun p -> op2_scan_pat pdata p) pat_list)
      | x -> x

  and op2_scan_guard pdata =
    function
        (GD.Guard gde, exp) -> (GD.Guard (scan_exp0 pdata gde), scan_exp_top pdata exp)

  and op2_scan_rhs pdata =
      function
          D.Rhs (exp, None) -> D.Rhs (scan_exp_top pdata exp, None)
        | D.Rhs (exp, Some exp_decl_list) -> D.Rhs (scan_exp_top pdata exp, Some (L.map (op2_scan_decl pdata) exp_decl_list))
        | D.RhsWithGD (gdrhs_list, None) -> D.RhsWithGD (L.map (op2_scan_guard pdata) gdrhs_list, None)
        | D.RhsWithGD (gdrhs_list, Some exp_decl_list) -> D.RhsWithGD (L.map (op2_scan_guard pdata) gdrhs_list, Some (List.map (op2_scan_decl pdata) exp_decl_list))

  and op2_scan_decl pdata =
    function
        D.FunDec deflist -> D.FunDec (L.map (fun (lhs, rhs) -> (op2_scan_funlhs pdata lhs), (op2_scan_rhs pdata rhs)) deflist)
      | D.PatBind (pat, rhs) -> D.PatBind ((op2_scan_pat pdata pat), (op2_scan_rhs pdata rhs))
      | x -> x

  and op2_scan_cdecl pdata tcls =
    function
        D.FunDecC deflist -> D.FunDecC (L.map (fun (lhs, rhs) -> (op2_scan_funlhs pdata lhs), (op2_scan_rhs pdata rhs)) deflist)
      | x -> x

  and op2_scan_idecl pdata tcls =
    function
        D.FunDecI deflist -> D.FunDecI (L.map (fun (lhs, rhs) -> (op2_scan_funlhs pdata lhs), (op2_scan_rhs pdata rhs)) deflist)
      | x -> x

  and op2_scan_topdecl pdata =
    function 
        D.Decl d -> D.Decl (op2_scan_decl pdata d)
      | D.Class (ctx, ((cls, _) as cls_wl), x, cdecl_list) ->
          let new_cdecl_list = List.map (fun cdecl -> op2_scan_cdecl pdata (ID.class_find cls) cdecl) cdecl_list in
            D.Class (ctx, cls_wl, x, new_cdecl_list)
      | D.Instance (ctx, ((cls, _) as cls_wl), x, idecl_list) ->
          let new_idecl_list = List.map (fun idecl -> op2_scan_idecl pdata (ID.class_find cls) idecl) idecl_list in
            D.Instance (ctx, cls_wl, x, new_idecl_list)
      | x -> x

  and op2_scan_module pdata =
    function
        (x, y, (z, topdecl_list)) -> (x, y, (z, List.map (op2_scan_topdecl pdata) topdecl_list))
    
end
