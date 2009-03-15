#! /bin/sh
set -e

PATH="/usr/bin:/bin"

make scratch.cma

if [ x$EMACS = x ]; then
	rl=rlwrap
fi

$rl ocaml str.cma -I `ocamlfind query extlib` extLib.cma scratch.cma
