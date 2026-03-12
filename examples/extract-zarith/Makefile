CAMLPKGS = rocq-runtime.kernel,rocq_verified_extraction.plugin,rocq_verified_extraction_ocaml_ffi

test: extract_nat_zarith.vo

extract_nat_zarith.vo: extract_nat_zarith.v
	rocq compile extract_nat_zarith.v
