
.PHONY: all

all: Makefile.rocq
	@make -f Makefile.rocq 

Makefile.rocq: _RocqProject
	@coq_makefile -f _RocqProject -o Makefile.rocq
