From VerifiedExtraction.Plugin Require Import Extract.
From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import bytestring.
From VerifiedExtraction.Plugin Require Import OCamlFFI.

Set Verified Extraction Build Directory "_build".

Definition hello_world :=
  print_string "Hello world!"%bs.

Verified Extraction -fmt -compile-with-coq -run hello_world "hello_world.mlf".
