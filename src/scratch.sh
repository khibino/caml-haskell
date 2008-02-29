#! /bin/sh

make layout.cma
rlwrap ocaml str.cma -I _build layout.cma
