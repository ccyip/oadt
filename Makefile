.DEFAULT_GOAL := all

%: Makefile.coq
	@$(MAKE) -f Makefile.coq $@

clean: cleanall
	$(RM) Makefile.coq Makefile.coq.conf
.PHONY: clean

Makefile.coq: _CoqProject
	@coq_makefile -f _CoqProject -o $@

Makefile _CoqProject: ;
