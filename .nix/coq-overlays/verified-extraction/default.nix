{
  lib,
  mkCoqDerivation,
  coq,
  dune_3,
  stdlib,
  ceres,
  equations,
  metarocq,
  malfunction,
  version ? null,
}:

(mkCoqDerivation {
  pname = "verified-extraction";
  owner = "MetaRocq";
  repo = "rocq-verified-extraction";
  opam-name = "rocq-verified-extraction";
  inherit version;
  defaultVersion = null;
  
  mlPlugin = true;
  useDune = false;
  
  buildInputs = [ dune_3 malfunction coq stdlib equations metarocq ceres ];
  propagatedBuildInputs = [ coq stdlib coq.ocamlPackages.ppx_optcomp coq.ocamlPackages.findlib malfunction ];

  meta = with lib; {
    homepage = "https://metarocq.github.io/";
    description = "Verified Extraction from Rocq to OCaml. Including a bootstrapped extraction plugin";
    maintainers = with maintainers; [ mattam82 ];
  };
})
