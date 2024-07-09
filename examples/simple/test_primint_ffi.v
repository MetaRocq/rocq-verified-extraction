From VerifiedExtraction.Plugin Require Import Extract.
From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Common Require Import Primitive.
From VerifiedExtraction.Plugin Require Import OCamlFFI.

Set Verified Extraction Build Directory "_build".

(* Primitives *)

From Coq Require Import PrimInt63 Uint63.

Definition foo : int := (300 / 80)%uint63. 

Set Warnings "-primitive-turned-into-axiom".

Definition prog := (print_int foo).

Verified Extraction -fmt -compile-with-coq -run prog "prim.mlf".

From Coq Require Import ZArith PrimInt63 Sint63 Uint63.

Verified Extraction -verbose Sint63.min_int.
Verified Extraction -verbose Sint63.max_int.
Verified Extraction -verbose Uint63.max_int.
Definition uint0 := Eval compute in (Uint63.of_Z 0%Z).
Verified Extraction -verbose uint0.
