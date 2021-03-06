
module F = Printf
module P = Parser
module L0 = Lexer0
module LST = LStream
module T = Token
module S = Stack
module SYN = Syntax
module ID = SYN.Identifier

exception Error of string

let debugFlag = ref false

let debug_out s =
  if !debugFlag then
    let _ = output_string stderr (s ^ "\n") in
      flush stderr

let new_err_flag () = ref false



let all_token_rev_list lexbuf =
  let unget_s = S.create () in
  let get_token () = L0.token lexbuf in
  let blk_level_pair tk =
    let loc = L0.get_location tk in (loc.T.start_p.T.col + 1, loc) in
  let eof_token_p = (function P.EOF(_) -> true | _ -> false) in

  let rec scan_start () =
    match get_token () with
        (P.SP_LEFT_BRACE _ | P.K_MODULE _) as start -> start
(*       | P.WS_NEWLINE _ -> scan_start () *)
      | P.WS_WHITE _ -> scan_start ()
      | other ->
          let _ = S.push other unget_s in
            P.BLK_OPEN (blk_level_pair other)
  in

  let scan_next prev = 
    let rec scan_next_rec () =
      let cur =
        if (S.is_empty unget_s) then (get_token ())
        else (S.pop unget_s) in

        match (prev, cur) with
            (_, (P.EOF(_) as eoft)) -> eoft
          | (_, P.WS_WHITE(_)) -> (scan_next_rec ())
(*        | (_, P.WS_NEWLINE(_)) -> (scan_next_rec ()) *)
          | ((P.K_LET(_) | P.K_WHERE(_) | P.K_DO(_) | P.K_OF(_)), (P.SP_LEFT_BRACE(_) as lbr)) -> lbr
          | ((P.K_LET(_) | P.K_WHERE(_) | P.K_DO(_) | P.K_OF(_)), tk) ->
              let (_, (level, loc)) = (S.push tk unget_s, blk_level_pair tk) in
                P.BLK_OPEN((if (eof_token_p tk) then 0 else level), loc)
          | (_, tk) ->
              let (_, loc) as p = blk_level_pair tk in
                if (loc.T.start_p.T.line
                    - (L0.get_location prev).T.end_p.T.line) > 0 then
                  let _ = S.push tk unget_s in P.BLK_LEVEL p
                else tk
    in (scan_next_rec ())
  in
    (* LST.create_stream (scan_start ()) scan_next eof_token_p *)
    (LST.fold_left
       (fun r a -> ((a, new_err_flag ()) :: r))
       []
       (LST.create_stream (scan_start ()) scan_next eof_token_p))

let rec layout istream levels =
  let push_new_token tok lform =
    LST.Cons ((tok, new_err_flag ()), lform)
  in

  let (tok, err) =
    match LST.peek istream with
        None -> raise Parsing.Parse_error
      | Some x -> x
  in
    match (tok, levels) with
        ((P.BLK_LEVEL (n, loc)), (m :: mstl as ms)) when m = n ->
          let addtk = P.SP_SEMI(loc) in
            push_new_token addtk (lazy (layout (LST.tl istream) ms))
      | ((P.BLK_LEVEL (n, loc)), m :: ms) when n < m  ->
          push_new_token (P.SP_RIGHT_BRACE(loc)) (lazy (layout istream ms))
      | ((P.BLK_LEVEL (n, _)), ms)                         -> layout (LST.tl istream) ms
      | ((P.BLK_OPEN (n, loc)), (m :: ms as levels)) when n > m  ->
          push_new_token (P.SP_LEFT_BRACE(loc)) (lazy (layout (LST.tl istream) (n :: levels))) (* Note 1 *)
      | ((P.BLK_OPEN (n, loc)), []) when n > 0             ->
          push_new_token (P.SP_LEFT_BRACE(loc)) (lazy (layout (LST.tl istream) [n])) (* Note 1 *)
      | ((P.BLK_OPEN (n, loc)), ms)                        ->
          push_new_token
            (P.SP_LEFT_BRACE(loc))
            (lazy (push_new_token
                     (P.SP_RIGHT_BRACE(loc))
                     (lazy (layout (push_new_token
                                      (P.BLK_LEVEL(n, loc))
                                      (lazy (LST.tl istream))) ms)))) (* Note 2 *)
      | ((P.SP_RIGHT_BRACE _ as rbr), 0 :: ms)        ->
          LST.Cons ((rbr, err), lazy (layout (LST.tl istream) ms)) (* Note 3 *)
      | ((P.SP_RIGHT_BRACE _), ms)                   -> raise Parsing.Parse_error (* Note 3 *)
      | ((P.SP_LEFT_BRACE _ as lbr), ms)             -> LST.Cons ((lbr, err), lazy (layout (LST.tl istream) (0 :: ms))) (* Note 4 *)

      | ((P.EOF loc as eoft), [])                    -> LST.Cons ((eoft, err), lazy (LST.Nil))
      | ((P.EOF loc), m :: ms) when m <> 0       -> push_new_token (P.SP_RIGHT_BRACE(loc)) (lazy (layout istream ms)) (* Note 6 *)

      | (t, (m :: mstl)) when m <> 0 && (!err)       ->
          err := false;
          push_new_token (P.SP_RIGHT_BRACE(L0.get_location t)) (lazy (layout istream mstl))  (* parse-error(t) Note 5 case *)
      | (t, ((m :: mstl) as ms))                   ->
          LST.Cons ((t, err),
                   lazy (layout (LST.tl istream) ms))
      | (t, ms)                                    ->
          LST.Cons ((t, err),
                   lazy (layout (LST.tl istream) ms))

type ('ret, 'tok) parse_result =
    Ret of 'ret | Err of 'tok

let create_input all_rev =
  LST.push_back_all all_rev LST.Nil

let make_context token_data =

  let lstream_ref = ref (layout (create_input token_data) []) in
  let lstream_next () =
    (match (LST.peek !lstream_ref) with
         None -> raise (Error "BUG! EOF handle")
       | Some x -> let _ = (lstream_ref := LST.tl !lstream_ref) in x)
  in
  let token_stack = S.create () in
    (lstream_next, token_stack)


let rec proceed_context (lstream_next, token_stack) =
  let (tok, _) as pair = lstream_next () in
  let _ = (S.push pair token_stack,
           debug_out (F.sprintf "token:%s" (L0.to_string_with_loc tok))) in
    tok
          
let try_parse token_data lexbuf =
  let context = make_context token_data in
    try
      Ret (P.e_module
             (fun _ -> proceed_context context)
             lexbuf)
    with
        Parsing.Parse_error ->
          let (cur_t, err) as et_pair = S.pop (snd context) in
          let _ = debug_out (F.sprintf "Error token:%s" (L0.to_string_with_loc cur_t)) in
            Err et_pair

let dump_tok_stream s =
  LST.fold_left
    (fun () (tok, loc) -> output_string stderr (L0.to_string_with_loc tok))
    ()
    s

let parse0 token_data lexbuf =

  let module_symbol =  
    let context = make_context token_data in
      try
        P.module_prefix
          (fun _ ->
             match proceed_context context with
               | P.SP_LEFT_BRACE (loc) | P.K_WHERE (loc) | P.SP_LEFT_PAREN (loc) -> P.EOF(loc)
               | tok -> tok
          )
          lexbuf
      with
          Parsing.Parse_error ->
            let (cur_t, err) = S.pop (snd context) in
              raise (Error (F.sprintf "Layout prefix parsing failed. Error token:%s" (L0.to_string_with_loc cur_t)))
  in

  let rec parse0 token_data lexbuf tryc et_list err_list =
    let _ = ID.begin_module_parse module_symbol in
    let _ = List.iter (fun e -> (e := true)) err_list in (* Set all errored token flags *)
      match (try_parse token_data lexbuf) with
        | Err (et, err) ->
            (if List.mem et et_list then
               let _ = debug_out (F.sprintf "Layout retrying %d failed." tryc) in
                 raise (Error (F.sprintf "Layout retrying %d failed. Error token:%s" tryc (L0.to_string_with_loc et)))
             else
               let _ = debug_out (F.sprintf "Layout retrying %d." (tryc + 1)) in
                 parse0 token_data lexbuf (tryc + 1) (et :: et_list) (err :: err_list))
        | Ret x -> x
  in
    parse0 token_data lexbuf 0 [] []

let parse0_str str =
  let lexbuf = (Lexing.from_string str) in
    parse0 (all_token_rev_list lexbuf) lexbuf


let parse0_chan input_chan =
  let lexbuf = (Lexing.from_channel input_chan) in
    parse0 (all_token_rev_list lexbuf) lexbuf

let parse_file f =
  parse0_chan (open_in_bin f)

let prelude_path = "./Prelude.hs"

let parse_prelude () =
   parse_file prelude_path

let rec parse_file_list loaded =
  function
    | [] -> loaded
    | f :: rest ->
        let syntax = parse_file f in
          parse_file_list (syntax :: loaded) rest

let parse_with_prelude input_chan =
  let pre = parse_prelude () in
    [ (parse0_chan input_chan); pre ]

let parse_files_with_prelude files =
  parse_file_list [parse_prelude ()] files

let parse_test fn =
  parse_with_prelude (open_in_bin fn)
