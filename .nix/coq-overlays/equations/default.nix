{
  lib,
  mkCoqDerivation,
  coq,
  stdlib,
  version ? null,
}:

(mkCoqDerivation {
  pname = "equations";
  owner = "mattam82";
  repo = "Coq-Equations";
  opam-name = "rocq-equations";
  inherit version;
  defaultVersion =
    let
      case = case: out: { inherit case out; };
    in
    lib.switch coq.coq-version [
      (case "9.1" "1.3.1+9.1")
      (case "9.0" "1.3.1+9.0")
    ] null;

  release."1.3.1+9.0".rev = "v1.3.1-9.0";
  release."1.3.1+9.0".sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
  release."1.3.1+9.1".rev = "v1.3.1-9.1";
  release."1.3.1+9.1".sha256 = "sha256-LtYbAR3jt+JbYcqP+m1n3AZhAWSMIeOZtmdSJwg7L1A=";

  mlPlugin = true;

  useDuneifVersion = v: v != null && (v == "dev" || lib.versionAtLeast v "1.3.1+9.0");

  propagatedBuildInputs = [ stdlib ];

  meta = {
    homepage = "https://mattam82.github.io/Coq-Equations/";
    description = "Plugin for Coq to add dependent pattern-matching";
    maintainers = with lib.maintainers; [ jwiegley ];
  };
}).overrideAttrs
  (
    o:
    if o.version != null && o.version != "dev" && !(lib.versionAtLeast o.version "1.3.1+9.0") then
      {
        preBuild = "coq_makefile -f _CoqProject -o Makefile${
          lib.optionalString (lib.versionAtLeast o.version "1.2.1" || o.version == "dev") ".coq"
        }";
      }
    else
      {
        propagatedBuildInputs = o.propagatedBuildInputs ++ [ coq.ocamlPackages.ppx_optcomp ];
      }
  )
