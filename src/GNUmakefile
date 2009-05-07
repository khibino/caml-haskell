PACKS=
CMAS= str,extLib
#OCAMLC=ocamlfind ocamlc -package ${PACKS}
#OCAMLC=ocamlfind ocamlc -g -I $(shell ocamlfind query extlib)

include ocaml_basic.gmk

ocaml_extra_load_path = -I $(shell ocamlfind query extlib)

scratch_sources = \
	token.ml onceAssoc.ml \
	syntax.ml \
	parseErr.ml \
	parser.ml \
	hsStr.ml \
	lexer0.ml \
	lStream.ml \
	layout.ml \
	eval.ml


mlis = parser.mli

sources = $(scratch_sources)

scratch_byte_objs = $(scratch_sources:.ml=.cmo)
scratch_nat_objs = $(scratch_sources:.ml=.cmx)

scratch_byte_lib = scratch.cma
scratch_nat_lib = scratch.cmxa scratch.a

%.lex0: %.hs
	./_build/lex0_main.byte < $< > $@ 2>&1

%.loin: %.hs
	./_build/loin_main.byte < $< > $@ 2>&1

%.layout: %.hs
	./_build/layout_main.byte < $< > $@ 2>&1

%.parse: %.hs
	./_build/parse_main.byte < $< > $@ 2>&1

#all: scratch.cma lex0_main.byte loin_main.byte layout_main.byte parse_main.byte fixity_main.byte eval_main.byte
all: scratch.cma 

test: clean all Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse

.depends: $(mlis)
	$(ocamldep) $(sources) $(mlis) > $@

$(scratch_byte_lib): $(scratch_byte_objs)
	$(ocamlc) -a -o $@ $^

$(scratch_nat_lib): $(scratch_nat_objs)
	$(ocamlopt) -a -o $@ $^

# eval.cma:
# 	ocamlbuild -verbose 1 -yaccflags -v -ocamlc '${OCAMLC}' eval.cma

# layout.cma:
# 	ocamlbuild -yaccflags -v -ocamlc '${OCAMLC}' layout.cma

#	ocamlbuild -yaccflags -v -ocamlc '${OCAMLC}' lexer0.cmo

include .depends

clean:
##	ocamlbuild -clean
	$(RM) *.cmi
	$(RM) *.cmo
	$(RM) *.cmx *.o
	$(RM) *.cma
	$(RM) parser.mli parser.ml lexer0.ml hsStr.ml
	$(RM) .depends
	$(RM) Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse
