{
  module LX = Lexing

  module S = Symbol
  module T = Token
  module P = Parser
  module F = Printf

  let dump_position pos =
    F.sprintf "(%d, %d, %d, %d)" pos.LX.pos_lnum (pos.LX.pos_cnum - pos.LX.pos_bol) pos.LX.pos_cnum pos.LX.pos_bol

  let fix_position lexbuf =
    let newline pos =
      { pos with
          LX.pos_lnum = pos.LX.pos_lnum + 1;
          LX.pos_cnum = pos.LX.pos_cnum + 1;
          LX.pos_bol = pos.LX.pos_cnum + 1;
      } in

    let tab pos =
      { pos with
          LX.pos_cnum = pos.LX.pos_cnum + 8 - (pos.LX.pos_cnum - pos.LX.pos_bol) mod 8
      } in

    let other pos =
      { pos with
          LX.pos_cnum = pos.LX.pos_cnum + 1
      } in

    let rec fix_pos_rec pos str =
      let len = (String.length str) in
        match (if len > 0 then (Some (str.[0]), String.sub str 1 (len - 1))
               else (None, "")) with
            (None, _) -> pos
          | (Some '\n', rest) -> fix_pos_rec (newline pos) rest
          | (Some '\t', rest) -> fix_pos_rec (tab pos) rest
          | (Some _, rest) -> fix_pos_rec (other pos) rest
    in
(*     let before = dump_position lexbuf.LX.lex_curr_p in *)
    let _ = lexbuf.LX.lex_curr_p <- fix_pos_rec (LX.lexeme_start_p lexbuf) (LX.lexeme lexbuf) in
(*     let after = dump_position lexbuf.LX.lex_curr_p in *)
(*     let _ = F.fprintf stdout "%s -> %s\n" before after in *)
      ()

  let loc lexbuf =
    let p2pos p = { T.col = p.LX.pos_cnum - p.LX.pos_bol; T.line = p.LX.pos_lnum } in
      { T.start_p = p2pos (LX.lexeme_start_p lexbuf); T.end_p = p2pos (LX.lexeme_end_p lexbuf) }

  let decode_with_mod lexbuf =
    let t = LX.lexeme lexbuf in
    let pp = String.index t '.' in
      { T.modid = S.intern (Str.string_before t pp);
        T.id    = S.intern (Str.string_after t pp) }

  let decode_cexpr cexpr =
    let fchar = String.get cexpr 0 in
    let escexp = String.sub cexpr 1 ((String.length cexpr) - 1) in
    let fmatch exp str = Str.string_match (Str.regexp exp) str 0 in
      if fchar = '\\' then
        match escexp with
            "NUL"   -> Some '\x00'
          | "SOH" | "^A"   -> Some '\x01'
          | "STX" | "^B"   -> Some '\x02'
          | "ETX" | "^C"   -> Some '\x03'
          | "EOT" | "^D"   -> Some '\x04'
          | "ENQ" | "^E"   -> Some '\x05'
          | "ACK" | "^F"   -> Some '\x06'
              
          | "BEL" | "^G" | "a"  -> Some '\x07'
          | "BS"  | "^H" | "b"  -> Some '\x08'
          | "HT"  | "^I" | "t"  -> Some '\t'
          | "LF"  | "^J" | "n"  -> Some '\n'
          | "VT"  | "^K" | "v"  -> Some '\x0b'
          | "FF"  | "^L" | "f"  -> Some '\x0c'
          | "CR"  | "^M" | "r"  -> Some '\r'
          | "SO"  | "^N"   -> Some '\x0e'
          | "SI"  | "^O"   -> Some '\x0f'
          | "DLE" | "^P"   -> Some '\x10'
              
          | "DC1" | "^Q"   -> Some '\x11'
          | "DC2" | "^R"   -> Some '\x12'
          | "DC3" | "^S"   -> Some '\x13'
          | "DC4" | "^T"   -> Some '\x14'
          | "NAK" | "^U"   -> Some '\x15'
          | "SYN" | "^V"   -> Some '\x16'
          | "ETB" | "^W"   -> Some '\x17'
          | "CAN" | "^X"   -> Some '\x18'
              
          | "EM"  | "^Y"   -> Some '\x19'
          | "SUB" | "^Z"   -> Some '\x1a'
          | "ESC" | "^["   -> Some '\x1b'
          | "FS"  | "^\\"  -> Some '\x1c'
          | "GS"  | "^]"   -> Some '\x1d'
          | "RS"  | "^^"   -> Some '\x1e'
          | "US"  | "^_"   -> Some '\x1f'
          | "SP"           -> Some ' '

          | "\\"           -> Some '\\'
          | "\""           -> Some '"'
          | "'"            -> Some '\''

          | "DEL"          -> Some '\x7f'

          | _ when fmatch "^[0-9]+$" escexp
              -> Some (Char.chr (int_of_string escexp))
          | _ when fmatch "^[xX][0-9a-zA-Z]+$" escexp 
              -> Some (Char.chr (int_of_string ("0" ^ escexp)))
          | _ when fmatch "^[oO][0-7]+$" escexp
              -> Some (Char.chr (int_of_string ("0" ^ escexp)))

          | _ -> None

      else Some fchar

  let decode_char lexbuf =
    let cstr = LX.lexeme lexbuf in
    let len = String.length cstr in
      match decode_cexpr (String.sub cstr 1 (len - 2)) with
          Some c -> c
        | None   -> failwith (F.sprintf "Unkown char expression %s" cstr)

  let decode_string lexbuf =
    let sexpr = LX.lexeme lexbuf in
    let len = String.length sexpr in
    let strlbuf = Lexing.from_string (String.sub sexpr 1 (len - 2)) in
    let rec decode result =
      match HsStr.char strlbuf with
          HsStr.Eos -> result
        | HsStr.Char cstr ->
            if cstr = "\\&" then decode (result ^ "&")
            else decode (result ^ 
                           match (decode_cexpr cstr) with
                               None -> failwith (F.sprintf "Unkown char expression '%s' in literal string" cstr)
                             | Some c -> (String.make 1 c))
        | HsStr.Gap g -> decode result
    in decode ""
}

let special = ['(' ')' ',' ';' '[' ']' '`' '{' '}']

let space = ' '
let newline = ("\r\n"|['\n' '\r'])
let tab = '\t'

let dashes = '-' '-' '-'*

let ascSmall = ['a'-'z']
let small = ascSmall | '_'
let ascLarge = ['A'-'Z']
let large = ascLarge

let plus = '+'
let minus = '-'
let exclamation = '!'
let ascSymbol_nbs = [ '!' '#' '$' '%' '&' '*' '+' '.' '/' '<' '=' '>' '?' '@' '^' '|' '-' '~' ]
let ascSymbol = ascSymbol_nbs | '\\'
let symbol = ascSymbol

let ascDigit = ['0'-'9']
let digit = ascDigit

let octit = ['0'-'7']
let hexit = ascDigit | ['a'-'z' 'A'-'Z']

let decimal = (digit)+
let octal = (octit)+
let hexadecimal = (hexit)+

let exponent = ['e' 'E'] ['+' '-']? decimal
let float = decimal '.' decimal exponent? | decimal exponent

let graphic = small | large | symbol | digit | special | [':' '"' '\'']
let any = graphic | space | tab

let comment = dashes ((space | tab | small | large | symbol | digit | special | [':' '"' '\'']) (any)*)? newline

let whitechar = newline | space | tab
let whitestuff = whitechar | comment 
let whitespace = (whitestuff)+

(*
let lwhitechar = space | tab
let lwhitestuff = lwhitechar | comment 
let lwhitespace = (lwhitestuff)+
*)

let char_gr = small | large | ascSymbol_nbs | digit | special | [':' '"']
let str_gr  = small | large | ascSymbol_nbs | digit | special | [':' '\'']

let charesc = ['a' 'b' 'f' 'n' 'r' 't' 'v' '\\' '"' '\'']
let str_charesc = charesc | '&'
let cntrl = ascLarge | ['@' '[' '\\' ']' '^' '_']
let gap = '\\' (whitechar)+ '\\'
(* let gap = '\\' (lwhitechar | newline)+ '\\' *)

let ascii = ('^' cntrl) | "NUL" | "SOH" | "STX" | "ETX" | "EOT" | "ENQ" | "ACK"
  | "BEL" | "BS" | "HT" | "LF" | "VT" | "FF" | "CR" | "SO" | "SI" | "DLE"
  | "DC1" | "DC2" | "DC3" | "DC4" | "NAK" | "SYN" | "ETB" | "CAN"
  | "EM" | "SUB" | "ESC" | "FS" | "GS" | "RS" | "US" | "SP" | "DEL"

let escape = '\\' ( charesc | ascii | decimal | 'o' octal | 'x' hexadecimal )
let str_escape = '\\' ( str_charesc | ascii | decimal | 'o' octal | 'x' hexadecimal )

let char = '\'' (char_gr | space | escape) '\''
let string = '"' (str_gr | space | str_escape | gap)* '"'

let varid = small (small | large | digit | '\'')*
let conid = large (small | large | digit | '\'')*

let varsym = symbol (symbol | ':')*
let consym = ':' (symbol | ':')*

let modid = conid

rule token = parse
  | '('  { P.SP_LEFT_PAREN(loc lexbuf) }
  | ')'  { P.SP_RIGHT_PAREN(loc lexbuf) }
  | ','  { P.SP_COMMA(loc lexbuf) }
  | ';'  { P.SP_SEMI(loc lexbuf) }
  | '['  { P.SP_LEFT_BRACKET(loc lexbuf) }
  | ']'  { P.SP_RIGHT_BRACKET(loc lexbuf) }
  | '`'  { P.SP_B_QUOTE(loc lexbuf) }
  | '{'  { P.SP_LEFT_BRACE(loc lexbuf) }
  | '}'  { P.SP_RIGHT_BRACE(loc lexbuf) }
      (** special tokens *)

  | "case"     { P.K_CASE(loc lexbuf) }
  | "class"    { P.K_CLASS(loc lexbuf) }
  | "data"     { P.K_DATA(loc lexbuf) }
  | "default"  { P.K_DEFAULT(loc lexbuf) }
  | "deriving" { P.K_DERIVING(loc lexbuf) }
  | "do"       { P.K_DO(loc lexbuf) }
  | "else"     { P.K_ELSE(loc lexbuf) }
  | "if"       { P.K_IF(loc lexbuf) }
  | "import"   { P.K_IMPORT(loc lexbuf) }
  | "in"       { P.K_IN(loc lexbuf) }
  | "infix"    { P.K_INFIX(loc lexbuf) }
  | "infixl"   { P.K_INFIXL(loc lexbuf) }
  | "infixr"   { P.K_INFIXR(loc lexbuf) }
  | "instance" { P.K_INSTANCE(loc lexbuf) }
  | "let"      { P.K_LET(loc lexbuf) }
  | "module"   { P.K_MODULE(loc lexbuf) }
  | "newtype"  { P.K_NEWTYPE(loc lexbuf) }
  | "of"       { P.K_OF(loc lexbuf) }
  | "then"     { P.K_THEN(loc lexbuf) }
  | "type"     { P.K_TYPE(loc lexbuf) }
  | "where"    { P.K_WHERE(loc lexbuf) }
  | "_"        { P.K_WILDCARD(loc lexbuf) }
      (** reservedid *)

  | ".."       { P.KS_DOTDOT(loc lexbuf) }
  | ":"        { P.KS_COLON(loc lexbuf) }
  | "::"       { P.KS_2_COLON(loc lexbuf) }
  | "="        { P.KS_EQ(loc lexbuf) }
  | "\\"       { P.KS_B_SLASH(loc lexbuf) }
  | "|"        { P.KS_BAR(loc lexbuf) }
  | "<-"       { P.KS_L_ARROW(loc lexbuf) }
  | "->"       { P.KS_R_ARROW(loc lexbuf) }
  | "@"        { P.KS_AT(loc lexbuf) }
  | "~"        { P.KS_TILDE(loc lexbuf) }
  | "=>"       { P.KS_R_W_ARROW(loc lexbuf) }
      (** reservedop *)

  | "as"              { P.K_AS(loc lexbuf) }  (** maybe varid *)
  | "qualified"       { P.K_QUALIFIED(loc lexbuf) }  (** maybe varid *)
  | "hiding"          { P.K_HIDING(loc lexbuf) }  (** maybe varid *)
  | varid      { P.T_VARID(S.intern (LX.lexeme lexbuf), loc lexbuf) }
  | conid      { P.T_CONID(S.intern (LX.lexeme lexbuf), loc lexbuf) }
      (** identifiers or may be qualified ones *)

  | whitespace  { fix_position lexbuf; P.WS_WHITE(loc lexbuf) }  (** comment begining with dashes is not varsym *)
(*   | lwhitespace  { fix_position lexbuf; P.WS_WHITE(loc lexbuf) }  (\** comment begining with dashes is not varsym *\) *)
(*   | newline      { fix_position lexbuf; P.WS_NEWLINE(loc lexbuf) } *)
      (** white spaces *)

  | plus       { P.KS_PLUS(loc lexbuf) }  (** maybe varsym *)
  | minus      { P.KS_MINUS(loc lexbuf) } (** maybe varsym *)
  | exclamation  { P.KS_EXCLAM(loc lexbuf) } (** maybe varsym *)
  | varsym     { P.T_VARSYM(S.intern (LX.lexeme lexbuf), loc lexbuf) }
  | consym     { P.T_CONSYM(S.intern (LX.lexeme lexbuf), loc lexbuf) }
      (** symbols or may be qualified ones *)

  | modid '.' varid   { P.T_MOD_VARID(decode_with_mod lexbuf, loc lexbuf) }
  | modid '.' conid   { P.T_MOD_CONID(decode_with_mod lexbuf, loc lexbuf) }
  | modid '.' varsym  { P.T_MOD_VARSYM(decode_with_mod lexbuf, loc lexbuf) }
  | modid '.' consym  { P.T_MOD_CONSYM(decode_with_mod lexbuf, loc lexbuf) }
      (** qualified xx *)

  | char      { P.L_CHAR(decode_char lexbuf, loc lexbuf) }
  | string    { fix_position lexbuf; P.L_STRING(decode_string lexbuf, loc lexbuf) }

  | decimal | ('0' ['o' 'O'] octal) | ('0' ['x' 'X'] hexadecimal)
        { P.L_INTEGER(Int64.of_string(LX.lexeme lexbuf), loc lexbuf) }

  | float      { P.L_FLOAT(float_of_string(LX.lexeme lexbuf), loc lexbuf) }

  | eof        { P.EOF(loc lexbuf) }

{

  let token_info tok =
    match tok with
        P.SP_LEFT_PAREN(loc) ->  "(", loc
      | P.SP_RIGHT_PAREN(loc) -> ")", loc
      | P.SP_COMMA(loc) -> ",", loc
      | P.SP_SEMI(loc)  -> ";", loc
      | P.SP_LEFT_BRACKET(loc) -> "[", loc
      | P.SP_RIGHT_BRACKET(loc) -> "]", loc
      | P.SP_B_QUOTE(loc) -> "`", loc
      | P.SP_LEFT_BRACE(loc) -> "{", loc
      | P.SP_RIGHT_BRACE(loc) -> "}", loc
      | P.K_CASE(loc) -> "case", loc
      | P.K_CLASS(loc) -> "class", loc
      | P.K_DATA(loc) -> "data", loc
      | P.K_DEFAULT (loc) -> "default", loc
      | P.K_DERIVING(loc) -> "deriving", loc
      | P.K_DO(loc) -> "do", loc
      | P.K_ELSE(loc) -> "else", loc
      | P.K_IF(loc) -> "if", loc
      | P.K_IMPORT(loc) -> "import", loc
      | P.K_IN(loc) -> "in", loc
      | P.K_INFIX(loc) -> "infix", loc
      | P.K_INFIXL(loc) -> "infixl", loc
      | P.K_INFIXR(loc) -> "infixr", loc
      | P.K_INSTANCE(loc) -> "instance", loc
      | P.K_LET(loc) -> "let", loc
      | P.K_MODULE(loc) -> "module", loc
      | P.K_NEWTYPE(loc) -> "newtype", loc
      | P.K_OF(loc) -> "of", loc
      | P.K_THEN(loc) -> "then", loc
      | P.K_TYPE(loc) -> "type", loc
      | P.K_WHERE(loc) -> "where", loc
      | P.K_WILDCARD(loc) -> "_", loc
      | P.KS_DOTDOT(loc) -> "..", loc
      | P.KS_COLON(loc) -> ":", loc
      | P.KS_2_COLON(loc) -> "::", loc
      | P.KS_EQ(loc) -> "=", loc
      | P.KS_B_SLASH(loc) -> "\\", loc
      | P.KS_BAR(loc) -> "|", loc
      | P.KS_L_ARROW(loc) -> "<-", loc
      | P.KS_R_ARROW(loc) -> "->", loc
      | P.KS_AT(loc) -> "@", loc
      | P.KS_TILDE(loc) -> "~", loc
      | P.KS_R_W_ARROW(loc) -> "=>", loc
      | P.K_AS(loc) -> "as", loc
      | P.K_QUALIFIED(loc) -> "qualified", loc
      | P.K_HIDING(loc) -> "hiding", loc
      | P.KS_PLUS(loc) -> "+", loc
      | P.KS_MINUS(loc) -> "-", loc
      | P.KS_EXCLAM(loc) -> "!", loc
      | P.T_VARID(n, loc) -> (S.name n), loc
      | P.T_CONID(n, loc) -> (S.name n), loc
      | P.T_CLSID(n, loc) -> "<class>:" ^ (S.name n), loc
      | P.T_VARSYM(n, loc) -> (S.name n), loc
      | P.T_CONSYM(n, loc) -> (S.name n), loc
      | P.T_MOD_VARID(wm, loc) -> T.with_mod_str wm, loc
      | P.T_MOD_CONID(wm, loc) -> T.with_mod_str wm, loc
      | P.T_MOD_CLSID(wm, loc) -> "<class>:" ^ T.with_mod_str wm, loc
      | P.T_MOD_VARSYM(wm, loc) -> T.with_mod_str wm, loc
      | P.T_MOD_CONSYM(wm, loc) -> T.with_mod_str wm, loc
      | P.L_CHAR(c, loc) -> Format.sprintf "'%c'" c, loc
      | P.L_STRING(s, loc) -> "\"" ^ s ^ "\"", loc
      | P.L_INTEGER(i64, loc) -> Int64.to_string i64, loc
      | P.L_FLOAT(f, loc) -> string_of_float f, loc
      | P.WS_WHITE(loc) -> "<WS>", loc
      | P.WS_NEWLINE(loc) -> "<NEWLINE>", loc

      | P.BLK_OPEN(lv, loc) -> Format.sprintf "{%d}" lv, loc
      | P.BLK_LEVEL(lv, loc) -> Format.sprintf "<%d>" lv, loc
      | P.EOF(loc) -> "<EOF>", loc


  let tkinfo_to_string = fst
  let tkinfo_to_loc = snd

  let to_string tok = tkinfo_to_string (token_info tok)
  let get_location tok = tkinfo_to_loc (token_info tok)

  let to_string_with_loc tok =
    let tkinfo = token_info tok in
      Format.sprintf "%s%s"
        (T.point_to_string (tkinfo_to_loc tkinfo).T.start_p)
        (tkinfo_to_string tkinfo)
}
