PLUGINPATH = ../../lib/coq_verified_extraction_plugin/_build/install/default/lib:../../lib/coq_verified_extraction_ocaml_ffi/_build/install/default/lib:../../lib/coq_verified_extraction_malfunction_ffi/_build/install/default/lib

all: Makefile.coq
	mkdir -p _build
	OCAMLPATH=$(PLUGINPATH) make -f Makefile.coq

install: Makefile.coq all
	make -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -rf _build