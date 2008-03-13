#! /bin/sh

PATH="/usr/bin:/bin"

make eval.cma
rlwrap ocaml str.cma -I `ocamlfind query extlib` extLib.cma -I _build eval.cma
