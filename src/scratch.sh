#! /bin/sh

make eval.cma
rlwrap ocaml str.cma -I /usr/lib/ocaml/3.10.0/extlib extLib.cma -I _build eval.cma
