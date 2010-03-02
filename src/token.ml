
module S = Symbol

type point = {
  col  : int;
  line : int;
}

type loc = {
  start_p : point;
  end_p   : point;
}

type id_with_mod = {
  modid : string;
  id : string;
}

let point_to_string p =
  Format.sprintf "%3d:%3d: " p.line p.col

let length loc =
  if (loc.start_p.line = loc.end_p.line) then
    (loc.end_p.col - loc.start_p.col)
  else
    -1

let implicit_loc =
  { start_p = { col = -1; line = -1 };
    end_p =  { col = -1; line = -1 };
  }

let plus_sym = S.intern "+"
let minus_sym = S.intern "-"
let exclam_sym = S.intern "!"

