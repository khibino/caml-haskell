##
##
##

stdlib_packages = \
	bigarray \
	num \
	str \
	unix \

stdlib_archives = \
	bigarray \
	nums \
	str \
	unix \
##	camlp4

extra_lib_packages =

extra_lib_archives =

ocaml_load_path = $(shell for l in $(stdlib_packages); do ocamlfind query -i-format $$l ; done | uniq) $(shell ocamlfind query -i-format camlp4)
ocaml_extra_load_path = $(shell for l in $(extra_lib_packages); do ocamlfind query -i-format $$l ; done | uniq)

ocamlyacc = ocamlyacc
ocamllex = ocamllex
ocamldep = ocamldep

ocamlc_debug = -g
#ocaml_warning = -w A
ocamlc_opt = $(ocaml_warning) $(ocamlc_debug)
ocamlc = ocamlc

byte_libs = $(stdlib_archives:=.cma) $(extra_lib_archives:=.cma)
BYTE_COMPILE.ml = $(ocamlc) $(ocamlc_opt) $(ocaml_load_path) $(ocaml_extra_load_path) -c
BYTE_LINK.ml = $(ocamlc) $(ocamlc_opt) $(ocaml_load_path) $(ocaml_extra_load_path)
BYTE_LINK.cmo = $(ocamlc) $(ocamlc_opt) $(ocaml_load_path) $(ocaml_extra_load_path)

INTERFACE.ml = $(ocamlc) $(ocamlc_opt) $(ocaml_load_path) $(ocaml_extra_load_path) -i


ocamlopt_opt = $(ocaml_warning)
ocamlopt = ocamlopt

nat_libs = $(stdlib_archives:=.cmxa) $(extra_lib_archives:=.cmxa)
NAT_COMPILE.ml = $(ocamlopt) $(ocamlopt_opt) $(ocaml_load_path) $(ocaml_extra_load_path) -c
NAT_LINK.ml = $(ocamlopt) $(ocamlopt_opt) $(ocaml_load_path) $(ocaml_extra_load_path)
NAT_LINK.cmx = $(ocamlopt) $(ocamlopt_opt) $(ocaml_load_path) $(ocaml_extra_load_path)


%.ml %.mli: %.mly
	$(ocamlyacc) $<

%.ml: %.mll
	$(ocamllex) $<

%.cmi: %.mli
	$(BYTE_COMPILE.ml) $<

%.cmo %.cmi: %.ml
	$(BYTE_COMPILE.ml) $< -o $@

%.cmx %.o %.cmi: %.ml
	$(NAT_COMPILE.ml) $< -o $@

%.mli: %.ml
	$(INTERFACE.ml) $< > $@

# info:
# 	@echo "byte_stdlibs = $(byte_stdlibs)"
# 	@echo "nat_stdlibs  = $(nat_stdlibs)"

# obj-clean:
# 	$(RM) *.cmi *.cmo *.cmx *.o

##
## end
##
