PLUGINPATH = ../../lib/coq_verified_extraction_plugin/_build/install/default/lib:../../lib/coq_verified_extraction_ocaml_ffi/_build/install/default/lib:../../lib/coq_verified_extraction_malfunction_ffi/_build/install/default/lib

all: Makefile.bootstrap Makefile.coq plugin
	
compile_malfunction.mlf: extract_extraction.v
	mkdir -p _build
	OCAMLPATH=$(PLUGINPATH) make -f Makefile.bootstrap
	cp _build/compile_malfunction.mlf compile_malfunction.mlf
	
plugin: compile_malfunction.mlf
	OCAMLPATH=$(PLUGINPATH) make -f Makefile.coq

install: Makefile.coq all
	make -f Makefile.coq install

Makefile.bootstrap: _BootstrapProject
	coq_makefile -f _BootstrapProject -o Makefile.bootstrap

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq Makefile.bootstrap
	make -f Makefile.bootstrap clean
	make -f Makefile.coq clean
	rm -rf _build