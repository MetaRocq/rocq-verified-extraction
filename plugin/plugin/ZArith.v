From MetaRocq Require Import Show.
From MetaRocq.Utils Require Import bytestring.
From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63 PrimString.
From Malfunction.Plugin Require Import Loader PrimInt63 PrimString.

(* https://github.com/ocaml/Zarith/blob/master/z.mli *)

Axiom t : Type.

Axiom zero : t.
Axiom one : t.
Axioms succ pred abs neg : t -> t.
Axioms add sub mul div rem : t -> t -> t.
Axiom pow : t -> int -> t.
Axiom equal : t -> t -> bool.
Axiom compare : t -> t -> int. (* int63 *)

Axiom of_int : int -> t.
Axiom of_string : string -> t.
Axiom to_string : t -> string.

Axioms logand logor logxor : t -> t -> t.
Axiom lognot : t -> t.

Axioms max min : t -> t -> t.
Axioms leq geq lt gt : t -> t -> bool.

Verified Extract Constants [
  t erased,
  zero => "Z.zero",
  one => "Z.one",
  succ => "Z.succ",
  pred => "Z.pred",
  abs => "Z.abs",
  neg => "Z.neg",
  add => "Z.add",
  sub => "Z.sub",
  mul => "Z.mul",
  div => "Z.div",
  rem => "Z.rem",
  pow => "Z.pow",

  logand => "Z.logand",
  logor => "Z.logor",
  logxor => "Z.logxor",
  lognot => "Z.lognot",

  max => "Z.max",
  min => "Z.min",

  leq => "Z.leq",
  geq => "Z.geq",
  lt => "Z.lt",
  gt => "Z.gt",

  compare => "Z.compare",

  of_int => "Z.of_int",
  of_string => "Z.of_string",
  to_string => "Z.to_string",

  equal => "Z.equal"
]
Packages [ "zarith" ].

Definition compare_signed x y := wrap_int (compare x y).

(* From Malfunction.Plugin Require Import OCamlFFI. *)
(* Set Verified Extraction Opam Path "/usr/local/bin/opam". *)

(* Definition test_zarith := *)
(*   print_string (show (equal (add zero one) zero)). *)

(* From MetaRocq.Utils Require Import monad_utils. *)
(* Import MRMonadNotation. *)
(* Print Instances Show. *)

(* Definition string_of_pstring (s : string) : bytestring.string := *)
(*   bytestring.String.concat bytestring.String.EmptyString (List.map char63_to_string (PrimStringAxioms.to_list s)). *)

(* Definition test_zarith2 := *)
(*   print_endline ("compare one zero = " ++ show (compare one zero)) ;; *)
(*   print_endline ("compare zero one = " ++ show (compare_signed zero one)) ;; *)
(*   print_endline ("compare one one = " ++ show (compare_signed one one)) ;; *)
(*   print_endline ("show pow 2 40 = " ++ string_of_pstring (to_string (pow (add one one) (of_string "40")))). *)

(* Verified Extraction -fmt -compile-with-coq *)
(*   -unsafe extract-inductives *)
(*   -run test_zarith2 "test_zarith2.mlf". *)
