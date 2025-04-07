all: coq extraction_plugin extraction_ocaml_ffi plugin bootstrap

extraction_ocaml_ffi:
	cd lib/coq_verified_extraction_ocaml_ffi && dune build

extraction_plugin:
	cd lib/coq_verified_extraction_plugin && dune build

coq: Makefile.rocq
	+make -f Makefile.rocq all

html: Makefile.rocq
	+make -f Makefile.rocq html

install: install-coq plugin

install-coq: Makefile.rocq coq
	+make -f Makefile.rocq install
	cd lib/coq_verified_extraction_ocaml_ffi && dune install
	cd lib/coq_verified_extraction_plugin && dune install
	cd plugin/plugin && make -f Makefile.rocq install
	cd plugin/plugin-bootstrap && make -f Makefile.rocq install

clean: Makefile.rocq plugin/plugin/Makefile.rocq plugin/plugin-bootstrap/Makefile.rocq
	+make -f Makefile.rocq clean
	rm -f Makefile.rocq
	rm -f Makefile.rocq.conf
	cd lib/coq_verified_extraction_ocaml_ffi && dune clean
	cd lib/coq_verified_extraction_plugin && dune clean
	cd plugin/plugin && make clean
	cd plugin/plugin-bootstrap && make clean

plugin/plugin/Makefile.rocq: plugin/plugin/_RocqProject
	cd plugin/plugin && make Makefile.rocq

plugin: coq plugin/plugin/Makefile.rocq extraction_plugin extraction_ocaml_ffi
	cd plugin/plugin && ./clean_extraction.sh
	+make -C plugin/plugin

test: 
	cd plugin/tests && make 

Makefile.rocq: _RocqProject
	coq_makefile -f _RocqProject -o Makefile.rocq

plugin/plugin-bootstrap/Makefile.rocq: plugin/plugin-bootstrap/_RocqProject
	cd plugin/plugin-bootstrap && make Makefile.rocq

bootstrap: coq plugin extraction_plugin extraction_ocaml_ffi
	+make -C plugin/plugin-bootstrap -j 1

.PHONY: extraction_plugin extraction_ocaml_ffi
