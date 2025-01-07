all: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

_CoqProject:;

Makefile.coq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all clean
