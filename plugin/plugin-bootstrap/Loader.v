Require Import String.
From MetaRocq.Template Require ExtractableLoader.

Declare ML Module "coq_verified_extraction.plugin".
Declare ML Module "coq-verified-extraction-malfunction.plugin".

(** This is required for linking with the OCaml FFIs which assume
    the ocaml ordering on [bool] values. *)
Verified Extract Inductives [ bool => "bool" [ 1 0 ] ].
