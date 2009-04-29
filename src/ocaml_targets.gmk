

%_byte: %.cmo
	$(BYTE_LINK.cmo) -o $@ $(byte_stdlibs) $^

%: %.cmx
	$(NAT_LINK.cmx) -o $@ $(nat_stdlibs) $^

