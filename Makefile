.DEFAULT_GOAL := all

COQMAKEFILE := Makefile.coq
COQDOCMAKEFILE ?= coqdocjs/Makefile.doc
COQDOCJS_CP := true
COQDOCJS_CUSTOM := doc
COQDOCEXTRAFLAGS := --external 'https://plv.mpi-sws.org/coqdoc/stdpp' stdpp

COQPROJECT ?= _CoqProject

-include $(COQDOCMAKEFILE)

%: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@

clean: cleanall
	$(RM) $(COQMAKEFILE) $(COQMAKEFILE).conf
.PHONY: clean

$(COQMAKEFILE): $(COQPROJECT) FORCE
	@coq_makefile -f $(COQPROJECT) -o $@

FORCE Makefile $(COQDOCMAKEFILE) _CoqProject: ;
