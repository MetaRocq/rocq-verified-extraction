From Malfunction.Plugin Require Import Extract OCamlFFI PrimString PrimInt63 ZArith Nat2ZArith.
From MetaRocq Require Import Show.
From MetaRocq.Utils Require Import bytestring.
From Corelib Require Import PrimString.

Set Verified Extraction Build Directory ".".
Set Verified Extraction Opam Path "/usr/local/bin/opam".

Definition string_of_pstring (s : string) : bytestring.string :=
  bytestring.String.concat bytestring.String.EmptyString (List.map char63_to_string (PrimStringAxioms.to_list s)).

Definition test_nat_zarith :=
  print_endline ("Nat.pow 2 40 = " ++ string_of_pstring (nat_to_string (Nat.pow 2 40)))%bs.

MetaRocq Run Print mli test_nat_zarith.

Verified Extraction -fmt -compile-with-coq -run -time
         -unsafe extract-inductives
         test_nat_zarith "test_nat_zarith.mlf".
