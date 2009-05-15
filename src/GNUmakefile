
include ocaml_targets.gmk
include ocaml_basic.gmk

ocaml_extra_inc_path = $(shell ocamlfind query -i-format extlib)
ocaml_extra_load_path = $(shell ocamlfind query -format "-I %d -ccopt -L%d" extlib)

scratch_sources = \
	util.ml \
	onceAssoc.ml orderedHash.ml \
	token.ml \
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

byte_libs = extLib.cma $(scratch_byte_lib)
nat_libs = extLib.cmxa $(scratch_nat_lib)

%.lex0: %.hs
	./lex0_main.byte < $< > $@ 2>&1

%.loin: %.hs
	./loin_main.byte < $< > $@ 2>&1

%.layout: %.hs
	./layout_main.byte < $< > $@ 2>&1

%.parse: %.hs
	./parse_main.byte < $< > $@ 2>&1

%.eval: %.hs
	./parse_eval.byte < $< > $@ 2>&1

all: all_byte all_nat

all_byte: scratch.cma lex0_main.byte loin_main.byte layout_main.byte parse_main.byte fixity_main.byte eval_main.byte

all_nat: scratch.cmxa lex0_main.nat loin_main.nat layout_main.nat parse_main.nat fixity_main.nat eval_main.nat

#all: scratch.cma 

info:
	echo "byte_libs = $(byte_libs)"

test: clean all Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse


.depends: $(mlis) $(sources)
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
	$(RM) *.byte
	$(RM) *.nat
	$(RM) *.cmi
	$(RM) *.cmo
	$(RM) *.cmx *.o
	$(RM) *.cma
	$(RM) parser.mli parser.ml lexer0.ml hsStr.ml
	$(RM) .depends
	$(RM) Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse
