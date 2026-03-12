From Malfunction.Plugin Require Import Loader ZArith.

(* https://github.com/ocaml/Zarith/blob/master/z.mli *)

Axiom case : forall (A : Type), nat -> (unit -> A) -> (nat -> A) -> A.
Axiom nat_to_string : nat -> PrimString.string.

Verified Extract Constants [
  case => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.case",
  Nat.add => "Z.add",
  Nat.mul => "Z.mul",
  Nat.pow => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.pow",
  Nat.eqb => "Z.equal",
  Nat.max => "Z.max",
  Nat.min => "Z.min",
  nat_to_string => "Z.to_string"
]
Packages [ "rocq_verified_extraction_ocaml_ffi", "zarith" ].

Verified Extract Inductives To Constants
  [ nat => [ [ ZArith.zero ZArith.succ | case ] ] ].
