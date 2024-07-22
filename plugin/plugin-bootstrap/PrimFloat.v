From VerifiedExtraction Require Loader.
From Coq.Floats Require Import PrimFloat.

Verified Extract Constants [ 
  Coq.Floats.PrimFloat.float erased,
  Coq.Floats.PrimFloat.compare => "Coq_verified_extraction_ocaml_ffi__Float64.compare",
  Coq.Floats.PrimFloat.eqb => "Coq_verified_extraction_ocaml_ffi__Float64.equal",
  Coq.Floats.PrimFloat.ltb => "Coq_verified_extraction_ocaml_ffi__Float64.lt",
  Coq.Floats.PrimFloat.leb => "Coq_verified_extraction_ocaml_ffi__Float64.le",
  Coq.Floats.PrimFloat.frshiftexp => "Coq_verified_extraction_ocaml_ffi__Float64.frshiftexp",
  Coq.Floats.PrimFloat.ldshiftexp => "Coq_verified_extraction_ocaml_ffi__Float64.ldshiftexp",
  Coq.Floats.PrimFloat.normfr_mantissa => "Coq_verified_extraction_ocaml_ffi__Float64.normfr_mantissa",
  Coq.Floats.PrimFloat.classify => "Coq_verified_extraction_ocaml_ffi__Float64.classify",
  Coq.Floats.PrimFloat.abs => "Coq_verified_extraction_ocaml_ffi__Float64.abs",
  Coq.Floats.PrimFloat.sqrt => "Coq_verified_extraction_ocaml_ffi__Float64.sqrt",
  Coq.Floats.PrimFloat.opp => "Coq_verified_extraction_ocaml_ffi__Float64.opp",
  Coq.Floats.PrimFloat.div => "Coq_verified_extraction_ocaml_ffi__Float64.div",
  Coq.Floats.PrimFloat.mul => "Coq_verified_extraction_ocaml_ffi__Float64.mul",
  Coq.Floats.PrimFloat.add => "Coq_verified_extraction_ocaml_ffi__Float64.add",
  Coq.Floats.PrimFloat.sub => "Coq_verified_extraction_ocaml_ffi__Float64.sub",
  Coq.Floats.PrimFloat.of_uint63 => "Coq_verified_extraction_ocaml_ffi__Float64.of_uint63",
  Coq.Floats.PrimFloat.next_up => "Coq_verified_extraction_ocaml_ffi__Float64.next_up",
  Coq.Floats.PrimFloat.next_down => "Coq_verified_extraction_ocaml_ffi__Float64.next_down" ]
Packages [ "coq_verified_extraction_ocaml_ffi" ].
