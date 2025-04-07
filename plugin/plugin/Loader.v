Require Import String.
From MetaRocq.Template Require ExtractableLoader.
From Malfunction Require Export PrintMli.

Declare ML Module "coq_verified_extraction.plugin".
Declare ML Module "coq-verified-extraction-ocaml.plugin".

(** This is required for linking with the OCaml FFIs which assume
    the ocaml ordering on [bool] values. *)
Verified Extract Inductives [ bool => "bool" [ 1 0 ] ].