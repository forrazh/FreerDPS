all: Makefile.rocq
	$(MAKE) -f Makefile.rocq all

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq cleanall

Makefile.rocq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.rocq

_CoqProject Makefile: ;

%: Makefile.rocq
	$(MAKE) -f Makefile.rocq $@

.PHONY: all clean
