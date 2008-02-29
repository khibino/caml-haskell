
module P = Parser
module L0 = Lexer0
module ST = LStream
module T = Token
module STK = Stack
module SYN = Syntax
module PBuf = SYN.ParseBuffer
module PD = SYN.ParsedData
module SS = SYN.Scan

exception Error of string

let debugFlag = ref false

let debug_out s =
  if !debugFlag then
    let _ = output_string stderr (s ^ "\n") in
      flush stderr

let new_err_flag () = ref false



let all_token_rev_list lexbuf =
  let unget_s = Stack.create () in
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
	  let _ = Stack.push other unget_s in
	    P.BLK_OPEN (blk_level_pair other)
  in

  let scan_next prev = 
    let rec scan_next_rec () =
      let cur =
	if (Stack.is_empty unget_s) then (get_token ())
	else (Stack.pop unget_s) in

	match (prev, cur) with
	    (_, (P.EOF(_) as eoft)) -> eoft
	  | (_, P.WS_WHITE(_)) -> (scan_next_rec ())
(* 	  | (_, P.WS_NEWLINE(_)) -> (scan_next_rec ()) *)
	  | ((P.K_LET(_) | P.K_WHERE(_) | P.K_DO(_) | P.K_OF(_)), (P.SP_LEFT_BRACE(_) as lbr)) -> lbr
	  | ((P.K_LET(_) | P.K_WHERE(_) | P.K_DO(_) | P.K_OF(_)), tk) ->
	      let (_, (level, loc)) = (Stack.push tk unget_s, blk_level_pair tk) in
		P.BLK_OPEN((if (eof_token_p tk) then 0 else level), loc)
	  | (_, tk) ->
	      let (_, loc) as p = blk_level_pair tk in
		if (loc.T.start_p.T.line
		    - (L0.get_location prev).T.end_p.T.line) > 0 then
		  let _ = Stack.push tk unget_s in P.BLK_LEVEL p
		else tk
    in (scan_next_rec ())
  in
    (* ST.create_stream (scan_start ()) scan_next eof_token_p *)
    (ST.fold_left
       (fun r a -> ((a, new_err_flag ()) :: r))
       []
       (ST.create_stream (scan_start ()) scan_next eof_token_p))

let create_input all_rev =
  ST.push_back_all all_rev ST.Nil

module SWL =
struct
  let get upper_levels =
    match upper_levels with
	[] -> ref []
      | (_, prev_stk) :: _ -> prev_stk

  let push tok stk =
    stk := (tok :: (!stk))
end

let push_new_token tok lform =
  ST.Cons ((tok, new_err_flag ()), lform)

let rec layout istream levels =
  let (tok, err) =
    match ST.peek istream with
	None -> raise Parsing.Parse_error
      | Some x -> x
  in
    match (tok, levels) with
	((P.BLK_LEVEL (n, loc)), (m :: mstl as ms)) when m = n ->
	  let addtk = P.SP_SEMI(loc) in
	    push_new_token addtk (lazy (layout (ST.tl istream) ms))
      | ((P.BLK_LEVEL (n, loc)), m :: ms) when n < m  ->
	  push_new_token (P.SP_RIGHT_BRACE(loc)) (lazy (layout istream ms))
      | ((P.BLK_LEVEL (n, _)), ms)                         -> layout (ST.tl istream) ms
      | ((P.BLK_OPEN (n, loc)), (m :: ms as levels)) when n > m  ->
	  push_new_token (P.SP_LEFT_BRACE(loc)) (lazy (layout (ST.tl istream) (n :: levels))) (* Note 1 *)
      | ((P.BLK_OPEN (n, loc)), []) when n > 0             ->
	  push_new_token (P.SP_LEFT_BRACE(loc)) (lazy (layout (ST.tl istream) [n])) (* Note 1 *)
      | ((P.BLK_OPEN (n, loc)), ms)                        ->
	  push_new_token
	    (P.SP_LEFT_BRACE(loc))
	    (lazy (push_new_token
		     (P.SP_RIGHT_BRACE(loc))
		     (lazy (layout (push_new_token
				      (P.BLK_LEVEL(n, loc))
				      (lazy (ST.tl istream))) ms)))) (* Note 2 *)
      | ((P.SP_RIGHT_BRACE _ as rbr), 0 :: ms)        ->
	  ST.Cons ((rbr, err), lazy (layout (ST.tl istream) ms)) (* Note 3 *)
      | ((P.SP_RIGHT_BRACE _), ms)                   -> raise Parsing.Parse_error (* Note 3 *)
      | ((P.SP_LEFT_BRACE _ as lbr), ms)             -> ST.Cons ((lbr, err), lazy (layout (ST.tl istream) (0 :: ms))) (* Note 4 *)

      | ((P.EOF loc as eoft), [])                    -> ST.Cons ((eoft, err), lazy (ST.Nil))
      | ((P.EOF loc), m :: ms) when m <> 0       -> push_new_token (P.SP_RIGHT_BRACE(loc)) (lazy (layout istream ms)) (* Note 6 *)

      | (t, (m :: mstl)) when m <> 0 && (!err)       ->
  	  err := false;
	  push_new_token (P.SP_RIGHT_BRACE(L0.get_location t)) (lazy (layout istream mstl))  (* parse-error(t) Note 5 case *)
      | (t, ((m :: mstl) as ms))                   ->
	  ST.Cons ((t, err),
		   lazy (layout (ST.tl istream) ms))
      | (t, ms)                                    ->
	  ST.Cons ((t, err),
		   lazy (layout (ST.tl istream) ms))

type ('ret, 'tok) parse_result =
    Ret of 'ret | Err of 'tok

let try_parse token_data lexbuf =

  let lstream_ref = ref (layout (create_input token_data) []) in

  let lstream_next () =
    (match (ST.peek !lstream_ref) with
	 None -> raise (Error "BUG! EOF handle")
       | Some x -> let _ = (lstream_ref := ST.tl !lstream_ref) in x) in

  let token_stack = Stack.create () in
      
  let rec proceed () =
    let (tok, _) as pair = lstream_next () in
    let _ = (Stack.push pair token_stack,
	     debug_out (Printf.sprintf "token:%s" (L0.to_string_with_loc tok))) in
      match tok with
	  P.T_CONID (n, loc) when PBuf.class_p (PBuf.local_module_name ()) n -> P.T_CLSID (n, loc)
	| P.T_MOD_CONID (iwm, loc) when PBuf.class_p iwm.T.modid iwm.T.id -> P.T_MOD_CLSID (iwm, loc)
	| _ -> tok
  in

    try
      Ret (Parser.e_module
	     (fun _ -> proceed ())
	     lexbuf)
    with
	Parsing.Parse_error ->
	  let (cur_t, err) as et_pair = Stack.pop token_stack in
	  let _ = debug_out (Printf.sprintf "Error token:%s" (L0.to_string_with_loc cur_t)) in
	    Err et_pair

let rec parse0 token_data lexbuf tryc et_list err_list =
  let _ = List.map (fun e -> (e := true)) err_list in (* Set all errored token flags *)
    match (try_parse token_data lexbuf) with
      | Err (et, err) ->
	  (if List.mem et et_list then
	     let _ = debug_out (Printf.sprintf "Layout retrying %d failed." tryc) in
	       raise (Error (Printf.sprintf "Layout retrying %d failed. Error token:%s" tryc (L0.to_string_with_loc et)))
	   else
	     let _ = debug_out (Printf.sprintf "Layout retrying %d." (tryc + 1)) in
	       parse0 token_data lexbuf (tryc + 1) (et :: et_list) (err :: err_list))
      | Ret x -> x

let parse0_str str =
  let lexbuf = (Lexing.from_string str) in
    parse0 (all_token_rev_list lexbuf) lexbuf 0 [] []


let parse0_chan input_chan =
  let lexbuf = (Lexing.from_channel input_chan) in
    parse0 (all_token_rev_list lexbuf) lexbuf 0 [] []


let dump_tok_stream s =
  ST.fold_left
    (fun () (tok, loc) -> print_endline (L0.to_string_with_loc tok))
    ()
    s

let debugFlagFixity = ref false

let parse pre_pd_opt input_chan =

  let prelude_mode =
    match pre_pd_opt with
	Some pre_pd -> false
      | None -> true
  in

  let parse_buffer =
    if prelude_mode then SYN.go_prelude_mode ()
    else PBuf.create () in
  let syntax = parse0_chan (input_chan) in
  let _ = SS.fixity_scan_module syntax in
  let debug = !debugFlagFixity in
  let _ =  if debug then
    let (modb, _) = (PBuf.find_module (PBuf.local_module_name ()),
		     print_endline "--- buffer dump ---") in
	PBuf.dump_module modb
  in
  let pd0 = SYN.create_parsed_data parse_buffer syntax in

  { pd0
    with
      PD.syntax
      = (SS.op2_scan_module
	   (pd0, (match pre_pd_opt with None -> pd0 | Some pre_pd -> pre_pd))
	   syntax)
  }

let prelude_path = "./Prelude.hs"

let parse_with_prelude input_chan =
  let pre_pd = parse None (open_in_bin prelude_path) in
    parse (Some pre_pd) input_chan

let parse_test fn =
  parse_with_prelude (open_in_bin fn)
