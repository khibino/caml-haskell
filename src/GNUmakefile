PACKS=
CMAS=str
#OCAMLC=ocamlfind ocamlc -package ${PACKS}
OCAMLC=ocamlfind ocamlc -g

%.byte:
	ocamlbuild -ocamlc '${OCAMLC}' -libs ${CMAS} $@

%.lex0: %.hs
	./_build/lex0_main.byte < $< > $@ 2>&1

%.loin: %.hs
	./_build/loin_main.byte < $< > $@ 2>&1

%.layout: %.hs
	./_build/layout_main.byte < $< > $@ 2>&1

%.parse: %.hs
	./_build/parse_main.byte < $< > $@ 2>&1

all: lex0_main.byte loin_main.byte layout_main.byte parse_main.byte fixity_main.byte

test: clean all Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse

layout.cma:
	ocamlbuild -yaccflags -v -ocamlc '${OCAMLC}' layout.cma

#	ocamlbuild -yaccflags -v -ocamlc '${OCAMLC}' lexer0.cmo

clean:
	ocamlbuild -clean
	$(RM) Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse
