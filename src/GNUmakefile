PACKS=
CMAS= str,extLib
#OCAMLC=ocamlfind ocamlc -package ${PACKS}
OCAMLC=ocamlfind ocamlc -g -I $(shell ocamlfind query extlib)

%.byte:
	ocamlbuild -ocamlc '${OCAMLC}' -lflags -I,/usr/lib/ocaml/3.10.0/extlib -libs ${CMAS} $@

%.lex0: %.hs
	./_build/lex0_main.byte < $< > $@ 2>&1

%.loin: %.hs
	./_build/loin_main.byte < $< > $@ 2>&1

%.layout: %.hs
	./_build/layout_main.byte < $< > $@ 2>&1

%.parse: %.hs
	./_build/parse_main.byte < $< > $@ 2>&1

all: eval.cma lex0_main.byte loin_main.byte layout_main.byte parse_main.byte fixity_main.byte

test: clean all Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse

eval.cma:
	ocamlbuild -verbose 1 -yaccflags -v -ocamlc '${OCAMLC}' eval.cma

layout.cma:
	ocamlbuild -yaccflags -v -ocamlc '${OCAMLC}' layout.cma

#	ocamlbuild -yaccflags -v -ocamlc '${OCAMLC}' lexer0.cmo

clean:
	ocamlbuild -clean
	$(RM) Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse
