module F = Printf
module T = Token
module L = List
module OH = OrderedHash
module S = Symbol

type ('k, 'v) ordh = ('k, 'v) OH.t

type fixity_lnr =
  | Infix
  | InfixLeft
  | InfixRight
      
let fixity_lnr_string =
  function
    | Infix -> "n"
    | InfixLeft -> "l"
    | InfixRight -> "r"

type fixity = (fixity_lnr * int)

let default_op_fixity = (InfixLeft, 9)

let fixity_str fix =
  F.sprintf "(%s,%d)" (fixity_lnr_string (fst fix)) (snd fix)

type tclass = {
  cname : string;
  type_var : string;
  ctxs : context_list;
}

and context_list =
    TClassCtx of (tclass list)

let tclass_str tc =
  (F.sprintf "(%s %s) => " tc.cname tc.type_var)

let tclass_context_str =
  function
      None -> ""
    | Some tc -> tclass_str tc

let the_prelude_name = "Prelude"
let the_prelude_symbol = S.intern the_prelude_name

(* let bool_true = S.intern "True" *)
let bool_long_true = S.intern "Prelude.True"
(* let bool_false = S.intern "False" *)
let bool_long_false = S.intern "Prelude.False"


let the_main_name = "Main"
let the_main_symbol = S.intern the_main_name
let the_entry_main_name = "main"
let the_entry_main_symbol = S.intern the_entry_main_name

type literal =
    Int of (int64)
  | Float of (float)
  | Char of (char)
  | String of (string)

type litwl = (literal * T.loc)

let unloc_literal = (fun l -> fst l)

let eq_literal aa bb = (aa = bb)

let must_be_int li err =
  match li with
      (Int (i64), _) -> Int64.to_int i64
    | _ -> failwith err


module Identifier =
struct

  module SAH = SaHashtbl
  module S = Symbol

  type sp_con =
    | Colon
    | Unit
    | NullList
    | Tuple of int

  let sp_con_str = function
    | Colon    -> ":"
    | Unit     -> "()"
    | NullList -> "[]"
    | Tuple i  -> ("(" ^ (Array.fold_left (^) "" (Array.make (i-1) ",")) ^ ")")

  type qualifier =
    | Unq of Symbol.t (* unqualified id has scope module name *)
    | Q   of Symbol.t

  type short =
    | N  of Symbol.t
    | Sp of sp_con

  type id = {
    short : short;
    qual  : qualifier;
  }

  let short id = id.short
  let qual  id = id.qual

  let short_sym id =
    match short id with
      | N n -> n
      | Sp sp -> S.intern (sp_con_str sp)

  let qual_sym id =
    match qual id with
      | Q m | Unq m -> m

  let pair_sym id =
    (qual_sym id, short_sym id)

  let long_name id =
    (S.name (qual_sym id)) ^ "."
    ^ (S.name (short_sym id))

  let long_sym id =
    S.intern (long_name id)

  let to_sym id =
    match qual id with
      | Q (_) -> long_sym id
      | _ -> short_sym id

  let parse_sym sym =
    let name = (S.name sym) in
    let matched =
      Str.string_match
        (Str.regexp "^\\([^.]+\\)\\.\\(.+\\)$")
        name
        0
    in
      if matched then (Some (S.intern (Str.matched_group 1 name)),
                       S.intern (Str.matched_group 2 name))
      else (None, sym)

  type idwl = (id * T.loc)
  type symwl = (Symbol.t * T.loc)


  let qualid q n =
    { short = N n;
      qual  = Q q;
    }

  let make_qual_id n q =
    qualid (S.intern q) (S.intern n)

  let unqualid n m = 
    { short = N   n;
      qual  = Unq m;
    }

  let make_unqual_id n m =
    unqualid (S.intern n) (S.intern m)

  let theModidStack : S.t Stack.t = Stack.create ()

  let begin_module_parse modid =
    Stack.push modid theModidStack;
    theModidStack

  let current_modid () =
    Stack.top theModidStack

  let unqualid_on_parse nsym =
    unqualid nsym (current_modid ())

  let make_unqual_id_on_parse n =
    unqualid
      (S.intern n)
      (current_modid ())

  let make_sp con =
    { short = Sp con;
      qual  = Unq the_prelude_symbol;
    }

  let sp_colon     = make_sp Colon    (* : *)
  let sp_unit      = make_sp Unit     (* () *)
  let sp_null_list = make_sp NullList (* [] *)
  let sp_tuple   i = make_sp (Tuple i)

  let idwl id loc = (id, loc)

  let make_unqual_idwl n m loc = idwl (make_unqual_id n m) loc

  let unqual_idwl_on_parse (nsym, loc) =
    idwl (unqualid_on_parse nsym) loc

  let make_unqual_idwl_on_parse n loc =
    idwl (make_unqual_id_on_parse n) loc

  let idwul id = idwl id T.implicit_loc

  let unloc idwl = fst idwl
  let eq_idwl aa bb = (unloc aa) = (unloc bb)

  let name_str id =
    match id.short, id.qual with
      | (Sp sp, _)   -> sp_con_str sp
      | (N n, Q m)   -> (S.name m) ^ "." ^ (S.name n)
      | (N n, _) (* (N n, Unq m) *) -> S.name n
(*       | (_, _) -> failwith "symbol name string unknown case." *)

  let name_sym id = S.intern (name_str id)

  let make_id_with_mod iwm = qualid iwm.T.modid iwm.T.id

  let make_idwl_with_mod (iwm, loc) = idwl (make_id_with_mod iwm) loc

end

module Module =
struct
  module ID = Identifier 

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
      IDec of (qual * ID.symwl * ID.symwl option * impspec option)
    | IEmpty

  type export =
      EVar of ID.idwl
    | ECons of (ID.idwl * symbols)
    | EClass of (ID.idwl * symbols)
    (* | EMod of ID.idwl *)
    | EMod of ID.symwl

end

module Pattern =
struct
  module ID = Identifier 

  type 'pat op2list_opf =
      Op2F of (ID.idwl * 'pat op2list_patf)
    | Op2End
  and 'pat op2list_patf =
      PatF of ('pat * 'pat op2list_opf)
    | Op2NoArg

  let uni_pat pat = PatF (pat, Op2End)
  let patf_cons pat op2 rest = PatF (pat, (Op2F (op2, rest)))
  let op2f_cons op2 pat rest = Op2F (op2, (PatF (pat, rest)))

  type pat =
      PlusP of (ID.idwl * int64 * T.loc)
    | VarP of ID.idwl
    | AsP of ID.idwl * pat
    | ConP of ID.idwl * pat list
    | LabelP of ID.idwl * (ID.idwl * pat) list
    | LiteralP of litwl
    | WCardP
    | TupleP of pat list
    | ListP of pat list
    | MIntP of (int64 * T.loc)
    | MFloatP of (float * T.loc)
    | Irref of pat

    | Pat0 of pat op2list_patf
    | Pat1 of pat op2list_patf

    | ConOp2P of (ID.idwl * pat * pat)

end

module Guard =
struct
  type 'exp t =
      Guard of 'exp
end

type 'exp gdrhs = ('exp Guard.t * 'exp) list

module Type =
struct
  module ID = Identifier 

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

  let maybe_class tycon tyvar =
    AppBT (simple_btype tycon, VarAT tyvar)

  let maybe_paren_class btype =
    AT (TT btype)

  let destruct_for_class =
    function
      | AppBT (BT (ConsAT (Qtycon tycon)), VarAT tyvar) ->
          (tycon, tyvar)
      | _ ->
          failwith "Type structure not applicable class."

  let destruct_for_paren_class =
    function
      | AT (TT btype) ->
          destruct_for_class btype
      | _ ->
          failwith "Type structure not applicable paren class."

  let maybe_classlist btype_list =
    TupleAT (List.map (fun btype -> TT btype) btype_list)

  let destruct_typ =
    function
      | TT (btype) -> btype
      |  _ ->
           failwith "Type is not normal type. (may be function type)"

  let destruct_for_classlist =
    function
      | TupleAT typ_list ->
          List.map (fun typ -> destruct_for_class (destruct_typ typ)) typ_list
      | _ ->
          failwith "Type structure not applicable class list."

  type arity =
      Lazy of typ
    | Strict of a_type

end

module Constructor =
struct
  module ID = Identifier 

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
  module ID = Identifier 

  type clazz =
      Class of (ID.idwl * ID.idwl)
    | ClassApp of (ID.idwl * ID.idwl * Type.a_type list)

  type context = clazz list
end

module Instance =
struct

  module ID = Identifier 

  type cons_arity =
      Type of (Type.cons * ID.idwl list)
    | Tuple of (ID.idwl list)
    | List of ID.idwl
    | Fun of (ID.idwl * ID.idwl)
end

module Decl =
struct
  module ID = Identifier
  module P = Pattern

  type gendecl =
    | TypeSig of (ID.idwl list * Context.context option * Type.typ)
    | Fixity of (fixity * ID.idwl list)
    | Empty

  type 'exp decl =
    | GenDecl of gendecl
    | FunDec of (('exp funlhs * 'exp rhs) list)
    | PatBind of (P.pat * 'exp rhs)

  (* Instance *)
  and 'exp i =
    | FunDecI of (('exp funlhs * 'exp rhs) list)
    | BindI of (ID.idwl * 'exp rhs)
    | EmptyI

  (* Class *)
  and 'exp c =
    | GenDeclC of gendecl
    | FunDecC of (('exp funlhs * 'exp rhs) list)
    | BindC of (ID.idwl * 'exp rhs)

  and 'exp rhs =
    | Rhs of ('exp * 'exp decl list option)
    | RhsWithGD of ('exp gdrhs * 'exp decl list option)

  and 'exp funlhs =
    | FunLV of (ID.idwl * P.pat list)
    | Op2Fun of (ID.idwl * (P.pat * P.pat))
    | NestDec of ('exp funlhs * P.pat list)

  let op2lhs_op lhsd = fst lhsd
  let op2lhs_left lhsd = fst (snd lhsd)
  let op2lhs_right lhsd = snd (snd lhsd)

  let op2lhs lhsd =
    let (op, _) as op_wl = op2lhs_op lhsd in
    (* let _ = ID.fun_regist op true in *)
      Op2Fun (op_wl, (P.Pat1 (op2lhs_left lhsd), P.Pat1 (op2lhs_right lhsd)))

  type 'exp top =
    | Type of (Type.typ * Type.typ)
    | Data of (Context.context * Type.typ * Constructor.con list * ID.idwl list)
    | NewType of (Context.context * Type.typ * Constructor.newcon * ID.idwl list)
    | Class of (Context.context * ID.idwl * ID.idwl * 'exp c list)
    | Instance of (Context.context * ID.idwl * Instance.cons_arity * 'exp i list)
    | Default of Type.typ list
    | Decl of 'exp decl

  let mk_class ctx ((name_id, _) as name_id_wl) ((typev_id, _) as typev_id_wl) def =
    (* let _ = F.fprintf stderr "mk_class: called with %s\n" (ID.name_str name_id) in *)
    (* let _ = ID.class_regist name_id { cname = ID.name_str name_id; type_var = ID.name_str typev_id; ctxs = TClassCtx [] } in *)
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
  module ID = Identifier 
  module P = Pattern
  module DS = DoStmt
  module A = Array

  type 'exp op2list_opf =
      Op2F of (ID.idwl * 'exp op2list_expf)
    | Op2End
  and 'exp op2list_expf =
      ExpF of ('exp * 'exp op2list_opf)
(*     | UniOpF of (ID.idwl * 'exp * 'exp op2list_opf) *)
    | Op2NoArg

  (*
    TODO:
    Using better abstraction.  (thanks sakaguchi-san)

    type ('a, 'b) mlist = Mcons of ('a * ('b, 'a) mlist) | Mnil 
    ...
    type 'exp op2list_expf = ('exp, ID.idwl) mlist
    type 'exp op2list_opf = (ID.idwl, 'exp) mlist
  *)

  let uni_exp exp = ExpF (exp, Op2End)
  let expf_cons exp op2 rest = ExpF (exp, (Op2F (op2, rest)))
  let op2f_cons op2 exp rest = Op2F (op2, (ExpF (exp, rest)))

  type aexp =
      VarE of ID.idwl (* qvar *)
    | ConsE of ID.idwl (* gcon *)
    | LiteralE of litwl
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

  let make_prelude_var_exp name =
    VarE (ID.idwul (ID.qualid the_prelude_symbol (S.intern name)))

end

module All =
struct
  module L = List

  module ID = Identifier
  module P = Pattern
  module GD = Guard
  module D = Decl
  module DS = DoStmt
  module E = Expression

  type 'module_buffer func = {
    module_buffer : 'module_buffer;
    op2_pat_n : int -> 'module_buffer func -> P.pat P.op2list_patf -> P.pat;
    op2_exp_0 : 'module_buffer func -> E.t E.op2list_expf -> E.t;
  }

  (* P.maptree_op2pat 0 func (maptree_pat func) patf *)
  (* P.maptree_op2pat 1 func (maptree_pat func) patf *)

  let lastScanBug = ref None

  let rec maptree_exp_top func =
      function
          E.Top (exp, x) -> E.Top ((maptree_exp0 func exp), x)
        | x -> lastScanBug := Some x; failwith "Syntax BUG!!"

  and maptree_exp10 func exp10 =
    (*  *)
    let maptree_atom_exp func =
      function
          E.ParenE exp -> E.ParenE (maptree_exp_top func exp)
        | E.TupleE elist -> E.TupleE (L.map (fun exp -> maptree_exp_top func exp) elist)
        | E.ListE elist -> E.ListE (L.map (fun exp -> maptree_exp_top func exp) elist)
        | x -> x
    in
    (*  *)
    let rec maptree_fun_exp func =
      function
          E.FfunE aexp -> E.FfunE (maptree_atom_exp func aexp)
        | E.FappE (fexp, aexp) -> E.FappE (maptree_fun_exp func fexp, maptree_atom_exp func aexp)
        | E.FappEID -> failwith "Syntax BUG!!. FappEID found."
    in
    match exp10 with
        E.LambdaE (x, exp) -> E.LambdaE (x, maptree_exp_top func exp)
      | E.LetE (decl_list, exp) -> E.LetE (L.map (maptree_decl func) decl_list, maptree_exp_top func exp)
      | E.IfE (pred, t, f) -> E.IfE (maptree_exp_top func pred, maptree_exp_top func t, maptree_exp_top func f)
      | E.CaseE (exp, x) -> E.CaseE (maptree_exp_top func exp, x)
      | E.DoE (stmt_list, exp) -> E.DoE (L.map (maptree_do_stmt func) stmt_list, maptree_exp_top func exp)
      | E.FexpE fexp -> E.FexpE (maptree_fun_exp func fexp)
      | x -> x

  and maptree_exp0 func =
      function
          E.Exp0 exp0 -> (func.op2_exp_0 func exp0)
        | x -> x

  and maptree_do_stmt func stmt =
    match stmt with
        DS.Exp (exp) -> DS.Exp (maptree_exp_top func exp)
      | DS.Cons (pat, exp) -> DS.Cons (maptree_pat func pat, maptree_exp_top func exp)
      | DS.Let (dlist) -> DS.Let (List.map (maptree_decl func) dlist)
      | DS.Empty -> DS.Empty

  and maptree_pat func =
    let rec  maptree_atompat func =
      function
          P.AsP (id, p) -> P.AsP (id, maptree_pat func p)
        | P.ConP (id, plist) -> P.ConP (id, L.map (fun p0 -> maptree_pat func p0) plist)
        | P.LabelP (id, idp_list) -> P.LabelP (id, (L.map (fun (id, p0) -> (id, maptree_pat func p0)) idp_list))
        | P.TupleP (plist) -> P.TupleP (L.map (fun p0 -> maptree_pat func p0) plist)
        | P.ListP  (plist) -> P.ListP  (L.map (fun p0 -> maptree_pat func p0) plist)
        | P.Irref (p) -> P.Irref (maptree_pat func p)
        | x -> x
    in
      function
        | P.Pat0 (patf) -> func.op2_pat_n 0 func patf
        | P.Pat1 (patf) -> func.op2_pat_n 1 func patf
        | p -> maptree_atompat func p

  and maptree_funlhs func =
    function
        D.FunLV (var, pat_list) ->
          D.FunLV (var, L.map (fun p -> maptree_pat func p) pat_list)
      | D.Op2Fun (varop, (pat_aa, pat_bb)) ->
          D.Op2Fun (varop, (maptree_pat func pat_aa, maptree_pat func pat_bb))
      | D.NestDec (lhs, pat_list) ->
          D.NestDec (maptree_funlhs func lhs, L.map (fun p -> maptree_pat func p) pat_list)

  and maptree_guard func =
    function
        (GD.Guard gde, exp) -> (GD.Guard (maptree_exp0 func gde), maptree_exp_top func exp)

  and maptree_rhs func =
      function
          D.Rhs (exp, None) -> D.Rhs (maptree_exp_top func exp, None)
        | D.Rhs (exp, Some exp_decl_list) -> D.Rhs (maptree_exp_top func exp, Some (L.map (maptree_decl func) exp_decl_list))
        | D.RhsWithGD (gdrhs_list, None) -> D.RhsWithGD (L.map (maptree_guard func) gdrhs_list, None)
        | D.RhsWithGD (gdrhs_list, Some exp_decl_list) -> D.RhsWithGD (L.map (maptree_guard func) gdrhs_list, Some (List.map (maptree_decl func) exp_decl_list))

  and maptree_decl func =
    function
        D.FunDec deflist -> D.FunDec (L.map (fun (lhs, rhs) -> (maptree_funlhs func lhs), (maptree_rhs func rhs)) deflist)
      | D.PatBind (pat, rhs) -> D.PatBind ((maptree_pat func pat), (maptree_rhs func rhs))
      | x -> x

  and maptree_cdecl func cls =
    function
        D.FunDecC deflist -> D.FunDecC (L.map (fun (lhs, rhs) -> (maptree_funlhs func lhs), (maptree_rhs func rhs)) deflist)
      | x -> x

  and maptree_idecl func cls =
    function
        D.FunDecI deflist -> D.FunDecI (L.map (fun (lhs, rhs) -> (maptree_funlhs func lhs), (maptree_rhs func rhs)) deflist)
      | x -> x

  and maptree_topdecl func =
    function 
        D.Decl d -> D.Decl (maptree_decl func d)
      | D.Class (ctx, ((cls, _) as cls_wl), x, cdecl_list) ->
          let new_cdecl_list = List.map (fun cdecl -> maptree_cdecl func cls cdecl) cdecl_list in
            D.Class (ctx, cls_wl, x, new_cdecl_list)
      | D.Instance (ctx, ((cls, _) as cls_wl), x, idecl_list) ->
          let new_idecl_list = List.map (fun idecl -> maptree_idecl func cls idecl) idecl_list in
            D.Instance (ctx, cls_wl, x, new_idecl_list)
      | x -> x

  and maptree_module func =
    function
        (x, y, (z, topdecl_list)) -> (x, y, (z, List.map (maptree_topdecl func) topdecl_list))
    
end
