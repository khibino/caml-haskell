
include ocaml_basic.mk

include ocaml_targets.mk

extra_lib_packages = extlib

extra_lib_archives = extLib

scratch_sources = \
	onceAssoc.ml \
	token.ml \
	parseErr.ml \
	syntax.ml \
	parser.ml \
	hsStr.ml \
	lexer0.ml \
	lStream.ml \
	layout.ml \
	eval.ml

##	fv.ml \


sources = \
	$(scratch_sources) \
	util.ml \
	lex0_main.ml \
	loin_main.ml \
	layout_main.ml \
	parse_main.ml \
	fixity_main.ml \
	eval_main.ml

mlis = parser.mli
cmis = $(sources:.ml=.cmi)

scratch_byte_objs = $(scratch_sources:.ml=.cmo)
scratch_nat_objs = $(scratch_sources:.ml=.cmx)

byte_objs = $(sources:.ml=.cmo)


%.lex0: %.hs
	./_build/lex0_main.byte < $< > $@ 2>&1

%.loin: %.hs
	./_build/loin_main.byte < $< > $@ 2>&1

%.layout: %.hs
	./_build/layout_main.byte < $< > $@ 2>&1

%.parse: %.hs
	./_build/parse_main.byte < $< > $@ 2>&1

all: scratch.cma lex0_main.byte loin_main.byte layout_main.byte parse_main.byte fixity_main.byte eval_main.byte

.depends: $(mlis)
	$(ocamldep) $(sources) $(mlis) > $@

-include .depends

test: clean all Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse

eval_main.byte: scratch.cma eval_main.cmo
	$(BYTE_LINK.cmo) -o $@ $(byte_libs) $^

scratch.cma: $(scratch_byte_objs)
	$(ocamlc) -a -o $@ $^


clean:
	$(RM) $(cmis) $(byte_objs)
	$(RM) $(mlis)
	$(RM) Prelude.lex0 Prelude.loin Prelude.layout Prelude.parse
