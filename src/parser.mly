%{
  module F = Printf
  module OH = OrderedHash

  module TK = Token
  module S = Syntax

  module PBuf = S.ParseBuffer

  module I = S.Identifier

  module D = S.Decl
  module M = S.Module
  module P = S.Pattern
  module DS = S.DoStmt
  module TY = S.Type
  module CON = S.Constructor
  module CTX = S.Context
  module INS = S.Instance
  module CA = S.Case
  module GD = S.Guard
  module LC = S.ListComp
  module E = S.Expression

  let debug_out_stream = stderr
  let debugFlag = ref false

  let debug_print =
    if !debugFlag then
      (fun str ->
         F.fprintf debug_out_stream "parser: %s\n" str; flush debug_out_stream)
    else
      (fun _ -> ())

  let debug_reduce to_ from =
    debug_print (F.sprintf "parser: %s <- %s" to_ from)

  let parse_error msg =
    debug_print "Parser.parse_error is called!!";
    ParseErr.parse_error_flag := true;
    ()

%}

%token  <Token.loc>  SP_LEFT_PAREN SP_RIGHT_PAREN SP_COMMA SP_SEMI SP_LEFT_BRACKET SP_RIGHT_BRACKET SP_B_QUOTE SP_LEFT_BRACE SP_RIGHT_BRACE

%token  <Token.loc>  K_CASE K_CLASS K_DATA K_DEFAULT  K_DERIVING K_DO K_ELSE

%token  <Token.loc>  K_IF K_IMPORT K_IN K_INFIX K_INFIXL K_INFIXR K_INSTANCE

%token  <Token.loc>  K_LET K_MODULE K_NEWTYPE K_OF K_THEN K_TYPE K_WHERE K_WILDCARD

%token  <Token.loc>  KS_DOTDOT KS_COLON KS_2_COLON KS_EQ KS_B_SLASH KS_BAR KS_L_ARROW KS_R_ARROW KS_AT KS_TILDE KS_R_W_ARROW

%token  <Token.loc>  K_AS K_QUALIFIED K_HIDING

%token  <Token.loc>  KS_PLUS KS_MINUS KS_EXCLAM

%token  <(Token.id_with_mod * Token.loc)>  T_MOD_CONSYM
%token  <(Token.id_with_mod * Token.loc)>  T_MOD_CONID T_MOD_CLSID
%token  <(string * Token.loc)>  T_CONSYM
%token  <(string * Token.loc)>  T_CONID T_CLSID

%token  <(Token.id_with_mod * Token.loc)>  T_MOD_VARSYM
%token  <(Token.id_with_mod * Token.loc)>  T_MOD_VARID
%token  <(string * Token.loc)>  T_VARSYM
%token  <(string * Token.loc)>  T_VARID

%token  <(char * Token.loc)>  L_CHAR
%token  <(string * Token.loc)>  L_STRING

%token  <(int64 * Token.loc)>  L_INTEGER
%token  <(float * Token.loc)>  L_FLOAT

%token  <Token.loc>  WS_WHITE WS_NEWLINE

%token  <(int * Token.loc)>  BLK_OPEN BLK_LEVEL

%token  <Token.loc>  EOF

%start  e_module
%type <((Symbol.t * Token.loc) * Syntax.Module.export list * (Syntax.Module.impdecl list * Syntax.Expression.t Syntax.Decl.top list))> e_module
/*  type e_module_type = (T.loc I.id * M.export list * (M.impdecl list * E.t D.top list)) */

%start  module_prefix
/*(*  %type <(Symbol.t * Token.loc) * Syntax.Module.export list> module_prefix  *)*/
/*(*  %type <Syntax.ParseBuffer.t> module_prefix  *)*/
%type <Symbol.t> module_prefix

%start  exp
%type <Syntax.Expression.t> exp

%%

e_module:
  module_top EOF { $1 }
;

module_top:
  K_MODULE modid export_list K_WHERE body { ($2, $3, $5) }
| K_MODULE modid K_WHERE body         { ($2, [], $4) }
| body { (I.idwul S.the_main_symbol,
          [M.EVar (I.idwul (I.make_qual_id S.the_main_name "main"))],
          $1) }
;

/*
module_prefix:
  K_MODULE modid export_list K_WHERE { ($2, $3) }
| K_MODULE modid K_WHERE             { ($2, []) }
| { (I.idwul S.the_main_symbol,
     [M.EVar (I.idwul (I.make_qual_id S.the_main_name "main"))]) }
;
*/

/*
module_prefix:
  K_MODULE modid export_list K_WHERE { PBuf.create (fst $2) }
| K_MODULE modid K_WHERE             { PBuf.create (fst $2) }
| { PBuf.create S.the_main_symbol }
;
*/

/*
module_prefix:
  K_MODULE modid  { PBuf.create (fst $2) }
| { PBuf.create S.the_main_symbol }
;
*/

module_prefix:
  K_MODULE modid  { fst $2 }
| { S.the_main_symbol }
;

body:
  /* SP_LEFT_BRACE topdecl_list SP_RIGHT_BRACE (n=0) case */
  /* SP_LEFT_BRACE impdecl_list SP_RIGHT_BRACE (n=1) empty impdecl case */
  SP_LEFT_BRACE SP_RIGHT_BRACE  { ([], []) }
  /* SP_LEFT_BRACE impdecl_list SP_SEMI topdecl_list SP_RIGHT_BRACE (n=0) and (n=1) empty impdecl case */
| SP_LEFT_BRACE SP_SEMI SP_RIGHT_BRACE  { ([], []) }
| SP_LEFT_BRACE impdecl_list SP_SEMI topdecl_list SP_RIGHT_BRACE  { (List.rev $2, $4) }
| SP_LEFT_BRACE impdecl_list SP_RIGHT_BRACE  { (List.rev $2, []) }
| SP_LEFT_BRACE topdecl_list SP_RIGHT_BRACE  { ([], $2) }
;

impdecl_list:
  le_impdecl_list SP_SEMI not_empty_impdecl  {  $3 :: $1 }
| impdecl_list SP_SEMI not_empty_impdecl  {  $3 :: $1 }
| not_empty_impdecl  { [$1] }
; /* topdecl <- gendecl may be empty, so remove last empty impdecl */

le_impdecl_list:
  le_impdecl_list SP_SEMI /* (empty declaration) */  { $1 }
| impdecl_list SP_SEMI /* (empty declaration) */  { $1 }
/* | (only one empty declaration)  { [] } */
;       /* (n>=1) */

export_list:
  SP_LEFT_PAREN export_comma_list may_comma SP_RIGHT_PAREN  { $2 }      /* (n>0) */
| SP_LEFT_PAREN may_comma SP_RIGHT_PAREN  { [] }        /* (n=0) */
;

export_comma_list:
  export SP_COMMA export_comma_list  { $1 :: $3 }
| export  { [$1] }
;

export:
  qvar  { M.EVar $1 }
| qtycon SP_LEFT_PAREN cname_list_or_dots SP_RIGHT_PAREN  { M.ECons ($1, $3) }  /* (n>0) */
| qtycon   { M.ECons ($1, M.List []) }  /* (n=0) */
| qtycls SP_LEFT_PAREN var_list_or_dots SP_RIGHT_PAREN  { M.EClass ($1, $3) }   /* (n>0) */
| qtycls   { M.EClass ($1, M.List []) } /* (n=0) */
| K_MODULE modid  { M.EMod $2 }
;

not_empty_impdecl:
  K_IMPORT may_qualified modid may_as_modid may_impspec  { M.IDec ($2, $3, $4, $5) }
;

/*
impdecl:
  K_IMPORT may_qualified modid may_as_modid may_impspec  { M.IDec ($2, $3, $4, $5) }
|   { M.IEmpty }                / * (empty declaration) * /
;
*/

may_qualified:
   { M.NotQual }
| k_qualified  { M.Qual }
;

may_as_modid:
   { None }
| k_as modid  { Some $2 }
;

may_impspec:
   { None }
| impspec  { Some $1 }
;

impspec:
  SP_LEFT_PAREN import_comma_list may_comma SP_RIGHT_PAREN  { M.Imp $2 }        /* (n>0) */
| SP_LEFT_PAREN may_comma SP_RIGHT_PAREN  { M.Imp [] }  /* (n=0) */
| k_hiding SP_LEFT_PAREN import_comma_list may_comma SP_RIGHT_PAREN  { M.Hide $3 }      /* (n>0) */
| k_hiding SP_LEFT_PAREN may_comma SP_RIGHT_PAREN  { M.Hide [] }        /* (n=0) */
;

may_comma:
   { false }
| SP_COMMA  { true }
;

import_comma_list:
  import SP_COMMA import_comma_list  { $1 :: $3 }
| import  { [$1] }
;

import:
  var  { M.IVar $1 }
| tycon SP_LEFT_PAREN cname_list_or_dots SP_RIGHT_PAREN  { M.ICons ($1, $3) }   /* (n>=0) */
| tycon  { M.ICons ($1, M.List []) }
| tycls SP_LEFT_PAREN var_list_or_dots SP_RIGHT_PAREN  { M.IClass ($1, $3) }    /* (n>=0) */
| tycls  { M.IClass ($1, M.List []) }
;

cname_list_or_dots:
  cname_comma_list  { M.List $1 }
|   { M.List [] }
| KS_DOTDOT  { M.All }
;

var_list_or_dots:
  var_list  { M.List $1 }
|   { M.List [] }
| KS_DOTDOT  { M.All }
;

cname_comma_list:
  cname SP_COMMA cname_comma_list  { $1 :: $3 }
| cname  { [$1] }
;

cname:
  var  { $1 }
| con  { $1 }
;

topdecl_list:
  topdecl_semi_list  { $1 }     /* (n>0) */
/* |   { [] }   (n=0) */
;

topdecl_semi_list:
  topdecl SP_SEMI topdecl_semi_list  { (* $1 :: $3 *) D.poly_fundec_cons $1 $3 D.defpair_from_topdecl D.topdecl_cons }
| topdecl  { [$1] }
;

topdecl:
  K_TYPE simpletype KS_EQ typ  { D.Type ($2, $4) }
| K_DATA simpletype KS_EQ constr_list may_have_deriving  { D.Data ([], $2, $4, $5) }
| K_DATA may_have_context simpletype KS_EQ constr_list may_have_deriving  { D.Data ($2, $3, $5, $6) }
| K_NEWTYPE simpletype KS_EQ newconstr may_have_deriving  { D.NewType ([], $2, $4, $5) }
| K_NEWTYPE may_have_context simpletype KS_EQ newconstr may_have_deriving  { D.NewType ($2, $3, $5, $6) }
| K_CLASS tycls tyvar may_have_cdecls  { D.mk_class [] $2 $3 $4 }
| K_CLASS may_have_scontext tycls tyvar may_have_cdecls  { D.mk_class $2 $3 $4 $5 }
| K_INSTANCE qtycls inst may_have_idecls  { D.Instance ([], $2, $3, $4) }
| K_INSTANCE may_have_scontext qtycls inst may_have_idecls  { D.Instance ($2, $3, $4, $5) }
| K_DEFAULT SP_LEFT_PAREN typ_comma_list SP_RIGHT_PAREN  { D.Default ($3) }     /* (n>0) */
| K_DEFAULT SP_LEFT_PAREN SP_RIGHT_PAREN  { D.Default ([]) }    /* (n=0) */
| decl  { D.Decl $1 }
;

may_have_deriving:
  deriving  { $1 }
|  { [] }
;

may_have_cdecls:
  K_WHERE cdecl_list  { $2 }
|   { [] }
;

may_have_idecls:
  K_WHERE idecl_list  { $2 }
|   { [] }
;

may_have_context:
  context KS_R_W_ARROW  { $1 }
/* |   { [] } */
;

may_have_scontext:
  scontext KS_R_W_ARROW  { $1 }
/* |   { [] } */
;

typ_comma_list:
  typ SP_COMMA typ_comma_list  { $1 :: $3 }
| typ  { [$1] }
;
                
decl_list:
  SP_LEFT_BRACE semi_decl_list SP_RIGHT_BRACE  { $2 }  /*(* (n>0) *)*/
| SP_LEFT_BRACE SP_RIGHT_BRACE  { [] }                 /*(* (n=0) *)*/
;

semi_decl_list:
  decl SP_SEMI semi_decl_list { (* $1 :: $3 *) D.poly_fundec_cons $1 $3 D.defpair_from_decl D.decl_cons }
| decl  { [$1] }
;

decl:
  gendecl  { D.GenDecl ($1) }
| funlhs rhs  { (* 4.4.3.1 関数束縛 *)     D.FunDec [($1, $2)] }
| pat0 rhs    { (* 4.4.3.2 パターン束縛 *) D.PatBind ($1, $2)  (* パターン x + i は pat0 になりえない。pat0 になりえるのは (x + i) *) }
;

cdecl_list:
  SP_LEFT_BRACE semi_cdecl_list SP_RIGHT_BRACE  { $2 }  /*(n>0)*/
| SP_LEFT_BRACE SP_RIGHT_BRACE  { [] }  /*(n=0)*/
;

semi_cdecl_list:
  cdecl SP_SEMI semi_cdecl_list { (* $1 :: $3 *) D.poly_fundec_cons $1 $3 D.defpair_from_c D.c_cons }
| cdecl  { [$1] }
;

cdecl:
  gendecl  { D.GenDeclC ($1) }
| funlhs rhs  { D.FunDecC [($1, $2)] }
| var rhs  { D.BindC ($1, $2) }
;

idecl_list:
  SP_LEFT_BRACE semi_idecl_list SP_RIGHT_BRACE  { $2 }  /*(n>0)*/
| SP_LEFT_BRACE SP_RIGHT_BRACE  { [] }  /*(n=0)*/
;

semi_idecl_list:
  idecl SP_SEMI semi_idecl_list  { (* $1 :: $3 *) D.poly_fundec_cons $1 $3 D.defpair_from_i D.i_cons }
| idecl  { [$1] }
;

idecl:
  funlhs rhs  { D.FunDecI [($1, $2)] }
| var rhs  { D.BindI ($1, $2) }
|   { D.EmptyI }                /*(empty)*/
;

gendecl:
  var_list KS_2_COLON context KS_R_W_ARROW typ  { D.TypeSig ($1, Some $3, $5) }         /* (type signature) */
| var_list KS_2_COLON typ  { D.TypeSig ($1, None, $3) }         /* (type signature) */
| fixity integer op_list  { D.Fixity (($1, (S.must_be_int $2 "Syntax Bug!")), $3) }     /* (fixity declaration) */
| fixity op_list  { D.Fixity (($1, 9), $2) }    /* (fixity declaration) */
|   { D.Empty }                 /* (empty declaration) */
;

op_list:
  /*op1 , ... , opn     (n>=1)*/
  op SP_COMMA op_list  { $1 :: $3 }
| op  { [$1] }
;

var_list:
  /*var1 , ..., varn    (n>=1)*/
  var SP_COMMA var_list  { $1 :: $3 }
| var  { [$1] }
;

fixity:
  K_INFIXL  { S.InfixLeft }
| K_INFIXR  { S.InfixRight }
| K_INFIX   { S.Infix }
;

context:
  typ_maybe_clazzlist    { List.map (fun tvpair -> CTX.Class tvpair) (TY.destruct_for_classlist $1) }
| typ_maybe_paren_clazz  { [ CTX.Class (TY.destruct_for_paren_class $1) ] }
| clazz  { [$1] }
| SP_LEFT_PAREN clazz_list SP_RIGHT_PAREN  { $2 }       /*(n>0)*/
| SP_LEFT_PAREN SP_RIGHT_PAREN  { [] }  /*(n=0)*/
;

typ:
  typ_maybe_clazz { $1 }
| typ_maybe_paren_clazz { $1 }
| typ_maybe_clazzlist { $1 }
| btype KS_R_ARROW typ  { TY.FunT ($1, $3) }    /*(function type)*/
| btype  { TY.TT $1 }
;

btype:
  btype atype  { TY.AppBT ($1, $2) }    /*(type application)*/
| atype  { TY.BT $1 }
;

atype:
  gtycon  { TY.ConsAT $1 }
| tyvar  { TY.VarAT $1 }
| SP_LEFT_PAREN typ_tupple_list SP_RIGHT_PAREN  { TY.TupleAT $2 }       /*(tuple type, k>=2)*/
| SP_LEFT_BRACKET typ SP_RIGHT_BRACKET  { TY.ListAT $2 }        /*(list type)*/
| SP_LEFT_PAREN typ SP_RIGHT_PAREN  { TY.AT $2 }        /*(parenthesized constructor)*/
;

typ_tupple_list:
  typ SP_COMMA typ_tupple_list  { $1 :: $3 }
| typ SP_COMMA typ  { [$1; $3] }
;

gtycon:
  qtycon  { TY.Qtycon $1 }
| SP_LEFT_PAREN SP_RIGHT_PAREN  { TY.UnitC }    /*(unit type)*/
| SP_LEFT_BRACKET SP_RIGHT_BRACKET  { TY.ListC }        /*(list constructor)*/
| SP_LEFT_PAREN KS_R_ARROW SP_RIGHT_PAREN  { TY.FunC }  /*(function constructor)*/
| SP_LEFT_PAREN comma_list SP_RIGHT_PAREN  { TY.TupleC $2 }     /*(tupling constructors)*/
;

clazz_list:
  clazz SP_COMMA clazz_list  { $1 :: $3 }
| clazz  { [$1] }
;

typ_maybe_clazz:
  qtycon tyvar { TY.maybe_class $1 $2 }
;

typ_maybe_paren_clazz:
  SP_LEFT_PAREN typ_maybe_clazz SP_RIGHT_PAREN { TY.maybe_paren_class $2 }
;

typ_maybe_clazz_comma_list:
  typ_maybe_clazz SP_COMMA typ_maybe_clazz_comma_list  { $1 :: $3 }
| typ_maybe_clazz SP_COMMA typ_maybe_clazz { [$1; $3] }
;

typ_maybe_clazzlist:
  SP_LEFT_PAREN typ_maybe_clazz_comma_list SP_RIGHT_PAREN { TY.maybe_classlist $2 }
;

clazz:
  typ_maybe_clazz { CTX.Class (TY.destruct_for_class $1) }
| qtycls tyvar  { CTX.Class ($1, $2) }
| qtycls SP_LEFT_PAREN tyvar atype_list SP_RIGHT_PAREN  { CTX.ClassApp($1, $3, $4) }    /*(n>=1)*/
;

atype_list:
  atype atype_list  { $1 :: $2 }
| atype  { [$1] }
;

scontext:
  simpleclass  { [$1] }
| SP_LEFT_PAREN simpleclass_list SP_RIGHT_PAREN  { $2 }         /* (n>0) */
| SP_LEFT_PAREN SP_RIGHT_PAREN  { [] }  /* (n=0) */
;

simpleclass_list:
  simpleclass SP_COMMA simpleclass_list  { $1 :: $3 }
| simpleclass  { [$1] }
;

simpleclass:
  qtycls tyvar  { CTX.Class ($1, $2) }
;

simpletype:
  tycon con_tyvar_list  { TY.TT ($2 (TY.simple_btype $1)) }     /* (k>0) */
| tycon  { TY.TT (TY.simple_btype $1) }         /* (k=0) */
;

con_tyvar_list:
  tyvar con_tyvar_list  { (fun bt -> $2 (TY.AppBT (bt, (TY.VarAT $1))))  }
| tyvar  { fun bt -> TY.AppBT (bt, (TY.VarAT $1)) }
;
/* bt t1  --  AppBT (bt, at1) */
/* bt at1 at2  --  AppBT (AppBT (bt, at1), at2) */
/* bt at1 at2 at3  --  AppBT (AppBT (AppBT (bt, at1), at2), at3) */
/* ... */


constr_list:
  constr KS_BAR constr_list  { $1 :: $3 }
| constr  { [$1] }
        /* (n>=1) */
;

constr:
  con arity_con_list  { CON.App ($1, $2) }      /* (arity con = k, k>0) */
| con   { CON.App ($1, []) }    /* (arity con = k, k=0) */
| b_or_strict_a conop b_or_strict_a  { CON.Op2 ($2, $1, $3) }   /* (infix conop) */
| con SP_LEFT_BRACE fielddecl_list SP_RIGHT_BRACE  { CON.Label ($1, $3) }       /* (n>0) */
| con SP_LEFT_BRACE SP_RIGHT_BRACE  { CON.Label ($1, []) }      /* (n=0) */
;

b_or_strict_a:
  btype  { TY.Lazy (TY.TT $1) }
| ks_exclam atype  { TY.Strict $2 }
;

arity_con_list:
  atype arity_con_list  { (TY.Lazy (TY.TT (TY.BT $1))) :: $2 }
| atype  { [TY.Lazy (TY.TT (TY.BT $1))] }
| ks_exclam atype arity_con_list  { (TY.Strict $2) :: $3 }
| ks_exclam atype  { [TY.Strict $2] }
;

fielddecl_list:
  fielddecl SP_COMMA fielddecl_list  { $1 :: $3 }
| fielddecl  { [$1] }
;

newconstr:
  con atype  { CON.Simple ($1, $2) }
| con SP_LEFT_BRACE var KS_2_COLON typ SP_RIGHT_BRACE  { CON.WithFLD ($1, $3, $5) }
;

fielddecl:
  var_list KS_2_COLON typ  { ($1, TY.Lazy $3) }
| var_list KS_2_COLON ks_exclam atype  { ($1, TY.Strict $4) }
;

deriving:
  K_DERIVING dclass  { [$2] }
| K_DERIVING SP_LEFT_PAREN dclass_list SP_RIGHT_PAREN  { $3 }   /* (n>0) */
| K_DERIVING SP_LEFT_PAREN SP_RIGHT_PAREN  { [] }       /* (n=0) */
;

dclass_list:
  dclass SP_COMMA dclass_list  { $1 :: $3 }
| dclass  { [$1] }
;

dclass:
  qtycls  { $1 }
;


inst:
  gtycon  { INS.Type ($1, []) }
| SP_LEFT_PAREN gtycon tyvar_list SP_RIGHT_PAREN  { INS.Type ($2, $3) }         /* (k>=0, tyvars distinct) */
| SP_LEFT_PAREN tyvar_comma_list SP_RIGHT_PAREN  { INS.Tuple $2 }       /* (k>=2, tyvars distinct) */
| SP_LEFT_BRACKET tyvar SP_RIGHT_BRACKET  { INS.List $2 }
| SP_LEFT_PAREN tyvar KS_R_ARROW tyvar SP_RIGHT_PAREN  { INS.Fun ($2, $4) }     /* (tyvar1 and tyvar2 distinct) */
;

tyvar_list:
  tyvar tyvar_list  { $1 :: $2 }
|   { [] }
;

tyvar_comma_list:
  tyvar SP_COMMA tyvar_comma_list  { $1 :: $3 }
| tyvar SP_COMMA tyvar  { [ $1; $3 ] }
;

/*
 funlhs          ->      var apat {apat }
        |       pati+1 varop(a,i) pati+1
        |       lpati varop(l,i) pati+1
        |       pati+1 varop(r,i) rpati
        |       ( funlhs ) apat {apat }
*/

funlhs:
  var apat_list  { I.fun_regist (I.unloc $1) true; D.FunLV($1, $2) }
| op2_pat_pair  { D.op2lhs $1 }
| SP_LEFT_PAREN funlhs SP_RIGHT_PAREN apat_list  { D.NestDec ($2, $4) }
;


/*(* 二項演算パターンのトップが最終的に関数束縛にされる *)*/
op2_pat_pair:
  ks_minus integer op2_pat_pair_right
    { let p = match $2 with (S.Int (x), loc) -> P.MIntP (x, loc) | _ -> failwith "negative integer literal pattern syntax error."
      in (D.op2lhs_op $3,
          (P.PatF (p, D.op2lhs_left $3),
           D.op2lhs_right $3))
    }
| ks_minus float op2_pat_pair_right
    { let p = match $2 with (S.Float (x), loc) -> P.MFloatP (x, loc) | _ -> failwith "negative integer literal pattern syntax error."
      in (D.op2lhs_op $3,
          (P.PatF (p, D.op2lhs_left $3),
           D.op2lhs_right $3))
    }
| pat10 op2_pat_pair_right  { (D.op2lhs_op $2,
                                (P.PatF ($1, D.op2lhs_left $2),
                                 D.op2lhs_right $2)) }

op2_pat_pair_right:
  qconop op2_pat_pair  { (D.op2lhs_op $2,
                          (P.Op2F ($1, (D.op2lhs_left $2)),
                           D.op2lhs_right $2))  }
| varop op2_patn_list  { ($1, (P.Op2End, $2)) }
;

rhs:
  KS_EQ exp K_WHERE decl_list  { D.Rhs ($2, Some $4)  }
| KS_EQ exp  { D.Rhs ($2, None)  }
| gdrhs K_WHERE decl_list  { D.RhsWithGD ($1, Some $3)  }
| gdrhs  { D.RhsWithGD ($1, None)  }
;

gdrhs:
  gd KS_EQ exp gdrhs  { ($1, $3) :: $4 }
| gd KS_EQ exp  { [($1, $3)] }
;

gd:
  KS_BAR exp0  { GD.Guard $2 }
;

exp:
  exp0  { E.Top ($1, None) }
| exp0 KS_2_COLON context KS_R_W_ARROW typ  { E.Top ($1, Some ($5, Some $3)) }  /*(expression type signature)*/
| exp0 KS_2_COLON typ  { E.Top ($1, Some ($3, None)) }  /*(expression type signature)*/
;

/*
lexp6:
  - exp7
;
*/

/*
expi    ->      expi+1 [qop(n,i) expi+1]
        |       lexpi
        |       rexpi
lexpi   ->      (lexpi | expi+1) qop(l,i) expi+1
rexpi   ->      expi+1 qop(r,i) (rexpi | expi+1)
*/

/*
exp0:   ->      [-] exp10 {qop [-] exp10}
*/

exp0:
  op2_expn_list  { E.Exp0 $1 }
;

op2_expn_list:
  ks_minus exp10 op2_right_section  { E.ExpF (E.Minus $2, $3) }
| exp10 op2_right_section  { E.ExpF ($1, $2) }
| ks_minus exp10  { E.ExpF (E.Minus $2, E.Op2End) }
| exp10  { E.ExpF ($1, E.Op2End) }
;

op2_right_section:
  qop op2_expn_list { E.Op2F ($1, $2) }
;

op2_left_section:
  ks_minus exp10 qop op2_left_section  { E.ExpF (E.Minus $2, E.Op2F ($3, $4)) }
| exp10 qop op2_left_section  { E.ExpF ($1, E.Op2F($2, $3)) }
| ks_minus exp10 qop  { E.ExpF (E.Minus $2, E.Op2F ($3, E.Op2NoArg)) }
| exp10 qop  { E.ExpF ($1, E.Op2F ($2, E.Op2NoArg)) }
;

exp10:
  KS_B_SLASH apat_list KS_R_ARROW exp  { E.LambdaE ($2, $4) }   /*(lambda abstraction, n>=1)*/
| K_LET decl_list K_IN exp  { E.LetE ($2, $4) }         /*(let expression)*/
| K_IF exp K_THEN exp K_ELSE exp  { E.IfE ($2, $4, $6) }        /*(conditional)*/
| K_CASE exp K_OF SP_LEFT_BRACE alt_list SP_RIGHT_BRACE  { E.CaseE ($2, $5) }   /*(case expression)*/
| K_DO SP_LEFT_BRACE stmt_list_exp SP_RIGHT_BRACE  { E.DoE $3 }         /*(do expression)*/
| fexp  { E.FexpE $1 }
;

/*
 fexp    ->      [fexp] aexp     (function application)
*/

fexp:
  aexp_list  { E.make_fexp $1 }
;

/*
aexp_list:
  aexp aexp_list  { $1 :: $2 }
| aexp  { [$1] }
;
*/

aexp_list:
  aexp aexp_list  { fun fexp -> $2 (E.FappE (fexp, $1)) }
| aexp  { fun fexp -> E.FappE (fexp, $1) }
;
/* fexp -- FfunE (fexp) */
/* fexp ae1 -- FappE (FfunE (fexp), ae1) */
/* fexp ae1 ae2 -- FappE (FappE (FfunE (fexp), ae1), ae2) */

/*
 aexp    ->      qvar    (variable)
        |       gcon    (general constructor)
        |       literal
        |       ( exp )         (parenthesized expression)
        |       ( exp1 , ... , expk )   (tuple, k>=2)
        |       [ exp1 , ... , expk ]   (list, k>=1)
        |       [ exp1 [, exp2] .. [exp3] ]     (arithmetic sequence)
        |       [ exp | qual1 , ... , qualn ]   (list comprehension, n>=1)
        |       ( expi+1 qop(a,i) )     (left section)
        |       ( lexpi qop(l,i) )      (left section)
        |       ( qop(a,i)<-> expi+1 )  (right section)
        |       ( qop(r,i)<-> rexpi )   (right section)
        |       qcon { fbind1 , ... , fbindn }  (labeled construction, n>=0)
        |       aexp<qcon> { fbind1 , ... , fbindn }    (labeled update, n >= 1)
*/



aexp:
  qvar  { E.VarE $1 }   /*(variable)*/
| gcon  { E.ConsE $1 }  /*(general constructor)*/
| literal  { E.LiteralE $1 }
| SP_LEFT_PAREN exp SP_RIGHT_PAREN  { E.ParenE $2 }     /*(parenthesized expression)*/
| SP_LEFT_PAREN exp SP_COMMA exp_list SP_RIGHT_PAREN  { E.TupleE ($2 :: $4) }   /*(tuple, k>=2)*/
| SP_LEFT_BRACKET exp_list SP_RIGHT_BRACKET  { E.ListE ($2) }   /*(list, k>=1)*/
| SP_LEFT_BRACKET exp KS_DOTDOT SP_RIGHT_BRACKET  { E.ASeqE($2, None, None) }   /*(arithmetic sequence)*/
| SP_LEFT_BRACKET exp SP_COMMA exp KS_DOTDOT SP_RIGHT_BRACKET  { E.ASeqE($2, Some $4, None) }   /*(arithmetic sequence)*/
| SP_LEFT_BRACKET exp KS_DOTDOT exp SP_RIGHT_BRACKET  { E.ASeqE($2, None, Some $4) }    /*(arithmetic sequence)*/
| SP_LEFT_BRACKET exp SP_COMMA exp KS_DOTDOT exp SP_RIGHT_BRACKET  { E.ASeqE($2, Some $4, Some $6) }    /*(arithmetic sequence)*/
| SP_LEFT_BRACKET exp KS_BAR qual_list SP_RIGHT_BRACKET  { E.LCompE ($2, $4) }  /*(list comprehension, n>=1)*/

| SP_LEFT_PAREN op2_left_section SP_RIGHT_PAREN  { E.MayLeftSecE ($2) }         /*(left section)*/
| SP_LEFT_PAREN op2_right_section SP_RIGHT_PAREN  { E.MayRightSecE ($2) }       /*(right section)*/

| qcon SP_LEFT_BRACE fbind_list SP_RIGHT_BRACE  { E.LabelConsE ($1, OH.of_list $3) }    /*(labeled construction, n>=1)*/
| qcon SP_LEFT_BRACE SP_RIGHT_BRACE  { E.LabelConsE ($1, OH.create 0) }         /*(labeled construction, n=0)*/
| aexp SP_LEFT_BRACE fbind_list SP_RIGHT_BRACE  { E.LabelUpdE ($1, OH.of_list $3) }     /*(labeled update, n >= 1)*/
;

exp_list:
  exp SP_COMMA exp_list  { $1 :: $3 }
| exp  { [$1] }
;

qual_list:
  qual SP_COMMA qual_list  { $1 :: $3 }
| qual  { [$1] }
;

fbind_list:
  fbind SP_COMMA fbind_list  { $1 :: $3 }
| fbind  { [$1] }
;

qual:
  pat KS_L_ARROW exp  { LC.Gen($1, $3) }        /*(generator)*/
| K_LET decl_list  { LC.Let $2 }        /*(local declaration)*/
| exp  { LC.Guard $1 }  /*(guard)*/
;

alt_list:
  alt SP_SEMI alt_list { $1 :: $3 }
| alt { [$1] }
;       /*(n>=1)*/

alt:
  pat KS_R_ARROW exp K_WHERE decl_list  { CA.Simple ($1, $3, $5) }
| pat KS_R_ARROW exp  { CA.Simple ($1, $3, []) }
| pat gdpat K_WHERE decl_list  { CA.WithGD ($1, $2, $4) }
| pat gdpat  { CA.WithGD ($1, $2, []) }
| { CA.Empty }          /*(empty alternative)*/
;

gdpat:
  gd KS_R_ARROW exp gdpat  { ($1, $3) :: $4 }
| gd KS_R_ARROW exp  { [($1, $3)] }
;

exp_may_be_semi:
  exp SP_SEMI  { $1 }
| exp  { $1 }
;

stmt_list_exp: /* stmts */
  stmt_list exp_may_be_semi  { (List.rev($1), $2) }     /*(n>=0)*/
;

stmt_list:
  stmt_list stmt { $2 :: $1 }
|   { [] }
;

stmt:
  exp SP_SEMI  { DS.Exp $1 }
| pat KS_L_ARROW exp SP_SEMI  { DS.Cons($1, $3) }
| K_LET decl_list SP_SEMI  { DS.Let $2 }
| SP_SEMI  { DS.Empty } /*(empty statement)*/
;

fbind:
  qvar KS_EQ exp { ($1, $3) }
;

pat:
  var ks_plus integer   /*(successor pattern)*/
      { match $3 with (S.Int (i), loc) -> P.PlusP($1, i, loc) | _ -> failwith "plus integer pattern syntax error." }
| pat0  { $1 }
;

/*
pati     ->      pati+1 [qconop(n,i) pati+1]
        |       lpati
        |       rpati
*/

/*
lpati   ->      (lpati | pati+1) qconop(l,i) pati+1
*/

/*
lpat6:
  ks_minus integer      (negative literal)
      { match $2 with (S.Int (v), l) -> S.P.MIntP (v, l) | _ -> failwith "negative integer literal pattern syntax error." }
| ks_minus float        (negative literal)
      { match $2 with (S.Float (v), l) -> S.P.MFloatP (v, l) | _ -> failwith "negative integer literal pattern syntax error." }
;
*/

/*
rpati   ->      pati+1 qconop(r,i) (rpati | pati+1)
*/

pat0:
  op2_patn_list  { P.Pat0 $1 }
;

op2_patn_list:
  ks_minus integer op2_patn_right
    { let p = match $2 with (S.Int (x), loc) -> P.MIntP (x, loc) | _ -> failwith "negative integer literal pattern syntax error."
      in P.PatF (p, $3)
    }
| ks_minus float op2_patn_right
    { let p = match $2 with (S.Float (x), loc) -> P.MFloatP (x, loc) | _ -> failwith "negative integer literal pattern syntax error."
      in P.PatF (p, $3)
    }
| pat10 op2_patn_right  { P.PatF ($1, $2) }
;

op2_patn_right:
  qconop op2_patn_list  { P.Op2F ($1, $2) }
|   { P.Op2End }
;

pat10:
  apat  { $1 }
| gcon apat_list        /*(arity gcon = k, k>=1)*/
      { P.ConP($1, $2) }
;

apat_list:
  apat apat_list { $1::$2 }
| apat           { [$1] }
;

apat:
  var
      { P.VarP $1 }
| var KS_AT apat        /*(as pattern)*/
      { P.AsP($1, $3) }
| gcon  /*(arity gcon = 0)*/
      { P.ConP($1, []) }
| qcon SP_LEFT_BRACE fpat_list SP_RIGHT_BRACE   /*(labeled pattern, k>=0)*/ /* may be error pattern */
      { P.LabelP($1, $3) }
| literal
      { P.LiteralP($1) }
| K_WILDCARD    /*(wildcard)*/
      { P.WCardP }
| SP_LEFT_PAREN pat SP_RIGHT_PAREN      /*(parenthesized pattern)*/
      { $2 }
| SP_LEFT_PAREN tuple_pat SP_RIGHT_PAREN        /*(tuple pattern, k>=2)*/
      { P.TupleP $2 }
| SP_LEFT_BRACKET list_pat SP_RIGHT_BRACKET     /*(list pattern, k>=1)*/
      { P.ListP $2 }
| KS_TILDE apat         /*(irrefutable pattern)*/
      { P.Irref $2 }
;

fpat_list:
  fpat SP_COMMA fpat_list  { $1::$3 }
| fpat   { [$1] }
|        { [] }
;

tuple_pat:
  pat SP_COMMA tuple_pat  { $1::$3 }
| pat SP_COMMA pat       { [$1; $3] }
;

list_pat:
  pat SP_COMMA list_pat  { $1 :: $3 }
| pat                    { [$1] }
;

fpat:
  qvar KS_EQ pat { ($1, $3) }
;

gcon:
  SP_LEFT_PAREN SP_RIGHT_PAREN  { I.idwl I.sp_unit $1 }
| SP_LEFT_BRACKET SP_RIGHT_BRACKET  { I.idwl I.sp_null_list $1 }
| SP_LEFT_PAREN comma_list SP_RIGHT_PAREN  { I.idwl (I.sp_tuple $2) $1 }
| qcon  { $1 }
;

comma_list:
  SP_COMMA comma_list  { 1 + $2 }
| SP_COMMA  { 1 }
;

qtyvar:
  qvarid  { $1 }         /*(qualified type variables)*/
;

qtycon:
  qconid  { $1 }        /*(qualified type constructors)*/
;

tyvar:
  varid  { $1 }          /*(type variables)*/
;

tycon:
  conid  { let (f, s) = $1 in I.make_unqual_idwl_on_parse f s }         /*(type constructors)*/
;

modid:
  conid  { let (f, s) = $1 in ((Symbol.intern f), s) }          /*(modules)*/
;

var:
  varid  { $1 }
| SP_LEFT_PAREN varsym SP_RIGHT_PAREN  { $2 }
;       /*(variable)*/

qvar:
  qvarid  { $1 }
| SP_LEFT_PAREN qvarsym SP_RIGHT_PAREN  { $2 }
;       /*(qualified variable)*/

con:
  conid  { let (f, s) = $1 in I.make_unqual_idwl_on_parse f s }
| SP_LEFT_PAREN consym SP_RIGHT_PAREN  { $2 }
;       /*(constructor)*/

qcon:
  qconid  { $1 }
| SP_LEFT_PAREN gconsym SP_RIGHT_PAREN  { $2 }
;       /*(qualified constructor)*/

varop:
  varsym  { $1 }
| SP_B_QUOTE varid SP_B_QUOTE  { $2 }
;       /*(variable operator)*/

qvarop:
  qvarsym  { $1 }
| SP_B_QUOTE qvarid SP_B_QUOTE  { $2 }
;       /*(qualified variable operator)*/

conop:
  consym  { $1 }
| SP_B_QUOTE conid SP_B_QUOTE  { let (f, s) = $2 in I.make_unqual_idwl_on_parse f s }
;       /*(constructor operator)*/

qconop:
  gconsym  { $1 }
| SP_B_QUOTE qconid SP_B_QUOTE  { $2 }
;       /*(qualified constructor operator)*/

op:
  varop  { $1 }
| conop  { $1 }
;       /*(operator)*/

qop:
  qvarop  { $1 }
| qconop  { $1 }
;       /*(qualified operator)*/


gconsym:
  KS_COLON  { I.idwl I.sp_colon $1 }
| qconsym   { $1 }
;

qvarid:
  T_MOD_VARID   { I.make_idwl_with_mod $1 }
| varid         { $1 }
;

qconid:
  T_MOD_CONID   { I.make_idwl_with_mod $1 }
| conid         { let (f, s) = $1 in I.make_unqual_idwl_on_parse f s }
;

qvarsym:
  T_MOD_VARSYM  { I.make_idwl_with_mod $1 }
| varsym        { $1 }
;

qconsym:
  T_MOD_CONSYM  { I.make_idwl_with_mod $1 }
| consym        { $1 }
;

varid:
  T_VARID  { I.make_unqual_idwl_on_parse (fst $1) (snd $1) }
| k_as         { $1 }
| k_qualified  { $1 }
| k_hiding     { $1 }
;

k_as:
  K_AS   { I.make_unqual_idwl_on_parse "as" $1 }
;

k_qualified:
  K_QUALIFIED   { I.make_unqual_idwl_on_parse "qulified" $1 }
;

k_hiding:
  K_HIDING   { I.make_unqual_idwl_on_parse "hiding" $1 }
;

qtycls:
  /* qconid  { $1 } */  /*(qualified type classes)*/
  T_MOD_CLSID   { I.make_idwl_with_mod $1 }
| tycls         { $1 }
;

tycls:
  conid  { let (f, s) = $1 in I.make_unqual_idwl_on_parse f s }         /*(type classes)*/
| T_CLSID  { I.make_unqual_idwl_on_parse (fst $1) (snd $1) }
;

conid:
  T_CONID  { $1 } /*(*{ let (f, s) = $1 in I.make_unqual_idwl_on_parse f s }*)*/
;

varsym:
  T_VARSYM  { I.make_unqual_idwl_on_parse (fst $1) (snd $1) }
| ks_plus    { $1 }
| ks_minus   { $1 }
| ks_exclam  { $1 }
;

ks_plus:
  KS_PLUS   { I.make_unqual_idwl_on_parse "+" $1 }
;

ks_minus:
  KS_MINUS  { I.make_unqual_idwl_on_parse "-" $1 }
;

ks_exclam:
  KS_EXCLAM  { I.make_unqual_idwl_on_parse "!" $1 }
;

consym:
  T_CONSYM  { I.make_unqual_idwl_on_parse (fst $1) (snd $1) }
;

literal:
  integer  { $1 }
| float    { $1 }
| char     { $1 }
| string   { $1 }
;

integer:
  L_INTEGER  { (S.Int(fst $1), (snd $1)) }
;

float:
  L_FLOAT  { (S.Float(fst $1), (snd $1)) }
;

char:
  L_CHAR  { (S.Char(fst $1), (snd $1)) }
;

string:
  L_STRING  { (S.String(fst $1), (snd $1)) }
;

/*                          */
/* end of parser.mly header */
/*                          */
