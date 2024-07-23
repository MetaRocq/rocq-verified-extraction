From Malfunction.Plugin Require Loader PrimInt63.
From Coq Require Import PArray.

(* This only interfaces with primitive integers, so no particular wrapping is needed. *)
(* However the polymorphic functions HAVE TO be masked to remove type argument 
  applications, hence typed erasure is required. *)

Verified Extract Constants [ 
  Coq.Array.PArray.array erased,
  Coq.Array.PArray.make => "Coq_verified_extraction_ocaml_ffi__Parray.make",
  Coq.Array.PArray.get => "Coq_verified_extraction_ocaml_ffi__Parray.get",
  Coq.Array.PArray.default => "Coq_verified_extraction_ocaml_ffi__Parray.default",
  Coq.Array.PArray.set => "Coq_verified_extraction_ocaml_ffi__Parray.set",
  Coq.Array.PArray.length => "Coq_verified_extraction_ocaml_ffi__Parray.length_int",
  Coq.Array.PArray.copy => "Coq_verified_extraction_ocaml_ffi__Parray.copy" ]
Packages [ "coq_verified_extraction_ocaml_ffi" ].
