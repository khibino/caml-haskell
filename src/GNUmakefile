
include ocaml_targets.gmk
include ocaml_basic.gmk

ocaml_extra_inc_path = $(shell ocamlfind query -i-format extlib)
ocaml_extra_load_path = $(shell ocamlfind query -format "-I %d -ccopt -L%d" extlib)

scratch_sources = \
	util.ml \
	symbol.ml \
	saHt.ml \
	saHashtbl.ml orderedHash.ml \
	token.ml \
	syntax.ml \
	parseErr.ml \
	parser.ml \
	hsStr.ml \
	lexer0.ml \
	lStream.ml \
	layout.ml \
	eval.ml


mlis = symbol.mli parser.mli


toplevel_sources = \
	lex0_main.ml \
	loin_main.ml \
	layout_main.ml \
	parse_main.ml \
	eval_main.ml

sources = \
	$(scratch_sources) \
	$(toplevel_sources)


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

%.debug: ../sample/%.hs
	OCAMLRUNPARAM=b ./eval_main.byte $< | 2>&1 tee $@

all: all_byte all_nat

all_byte: scratch.cma lex0_main.byte loin_main.byte layout_main.byte parse_main.byte fixity_main.byte eval_main.byte

all_nat: scratch.cmxa lex0_main.nat loin_main.nat layout_main.nat parse_main.nat fixity_main.nat eval_main.nat

#all: scratch.cma 

info:
	echo "byte_libs = $(byte_libs)"

test: all Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse
	for hs in p hello0 hello1 hello2 fixity fixity2 pat flip tak0 tak1; do \
		./eval_main.nat ../sample/$${hs}.hs; \
	done

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
	$(RM) *.cmo *.annot
	$(RM) *.cmx *.o
	$(RM) *.cma *.cmxa *.a
	$(RM) parser.mli parser.ml lexer0.ml hsStr.ml
	$(RM) .depends
	$(RM) Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse
