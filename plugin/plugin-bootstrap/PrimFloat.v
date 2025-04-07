From VerifiedExtraction Require Loader.
From Stdlib.Floats Require Import PrimFloat.

Verified Extract Constants [ 
  Stdlib.Floats.PrimFloat.float erased,
  Stdlib.Floats.PrimFloat.compare => "Rocq_verified_extraction_ocaml_ffi__Float64.compare",
  Stdlib.Floats.PrimFloat.eqb => "Rocq_verified_extraction_ocaml_ffi__Float64.equal",
  Stdlib.Floats.PrimFloat.ltb => "Rocq_verified_extraction_ocaml_ffi__Float64.lt",
  Stdlib.Floats.PrimFloat.leb => "Rocq_verified_extraction_ocaml_ffi__Float64.le",
  Stdlib.Floats.PrimFloat.frshiftexp => "Rocq_verified_extraction_ocaml_ffi__Float64.frshiftexp",
  Stdlib.Floats.PrimFloat.ldshiftexp => "Rocq_verified_extraction_ocaml_ffi__Float64.ldshiftexp",
  Stdlib.Floats.PrimFloat.normfr_mantissa => "Rocq_verified_extraction_ocaml_ffi__Float64.normfr_mantissa",
  Stdlib.Floats.PrimFloat.classify => "Rocq_verified_extraction_ocaml_ffi__Float64.classify",
  Stdlib.Floats.PrimFloat.abs => "Rocq_verified_extraction_ocaml_ffi__Float64.abs",
  Stdlib.Floats.PrimFloat.sqrt => "Rocq_verified_extraction_ocaml_ffi__Float64.sqrt",
  Stdlib.Floats.PrimFloat.opp => "Rocq_verified_extraction_ocaml_ffi__Float64.opp",
  Stdlib.Floats.PrimFloat.div => "Rocq_verified_extraction_ocaml_ffi__Float64.div",
  Stdlib.Floats.PrimFloat.mul => "Rocq_verified_extraction_ocaml_ffi__Float64.mul",
  Stdlib.Floats.PrimFloat.add => "Rocq_verified_extraction_ocaml_ffi__Float64.add",
  Stdlib.Floats.PrimFloat.sub => "Rocq_verified_extraction_ocaml_ffi__Float64.sub",
  Stdlib.Floats.PrimFloat.of_uint63 => "Rocq_verified_extraction_ocaml_ffi__Float64.of_uint63",
  Stdlib.Floats.PrimFloat.next_up => "Rocq_verified_extraction_ocaml_ffi__Float64.next_up",
  Stdlib.Floats.PrimFloat.next_down => "Rocq_verified_extraction_ocaml_ffi__Float64.next_down" ]
Packages [ "coq_verified_extraction_ocaml_ffi" ].
