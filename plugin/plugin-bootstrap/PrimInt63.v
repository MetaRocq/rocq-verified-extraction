From VerifiedExtraction Require Loader.
Require Int63.PrimInt63.

(** Primitive ints *)
Verified Extract Constants [
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.int erased,
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.add => "Rocq_verified_extraction_ocaml_ffi__Uint63.add",
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.sub => "Rocq_verified_extraction_ocaml_ffi__Uint63.sub", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.mul => "Rocq_verified_extraction_ocaml_ffi__Uint63.mul", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.div => "Rocq_verified_extraction_ocaml_ffi__Uint63.div", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.mod => "Rocq_verified_extraction_ocaml_ffi__Uint63.rem", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.lsl => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_sl", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.lsr => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_sr", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.land => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_and",
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.lxor => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_xor",
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.lor => "Rocq_verified_extraction_ocaml_ffi__Uint63.l_or",
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.asr => "Rocq_verified_extraction_ocaml_ffi__Uint63.a_sr",
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.head0 => "Rocq_verified_extraction_ocaml_ffi__Uint63.head0", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.tail0 => "Rocq_verified_extraction_ocaml_ffi__Uint63.tail0", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.eqb => "Rocq_verified_extraction_ocaml_ffi__Uint63.equal",
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.compare => "Rocq_verified_extraction_ocaml_ffi__Uint63.compare", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.compares => "Rocq_verified_extraction_ocaml_ffi__Uint63.compares", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.addc => "Rocq_verified_extraction_ocaml_ffi__Uint63.addc", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.addcarryc => "Rocq_verified_extraction_ocaml_ffi__Uint63.addcarryc", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.subc => "Rocq_verified_extraction_ocaml_ffi__Uint63.subc",
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.subcarryc => "Rocq_verified_extraction_ocaml_ffi__Uint63.subcarryc", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.mulc => "Rocq_verified_extraction_ocaml_ffi__Uint63.mulc", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.divs => "Rocq_verified_extraction_ocaml_ffi__Uint63.divs", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.mods => "Rocq_verified_extraction_ocaml_ffi__Uint63.rems", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21 => "Rocq_verified_extraction_ocaml_ffi__Uint63.div21", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.diveucl => "Rocq_verified_extraction_ocaml_ffi__Uint63.diveucl", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.addmuldiv => "Rocq_verified_extraction_ocaml_ffi__Uint63.addmuldiv", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.leb => "Rocq_verified_extraction_ocaml_ffi__Uint63.le", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.ltb => "Rocq_verified_extraction_ocaml_ffi__Uint63.lt", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.ltsb => "Rocq_verified_extraction_ocaml_ffi__Uint63.lts", 
  Stdlib.Numbers.Cyclic.Int63.PrimInt63.lesb => "Rocq_verified_extraction_ocaml_ffi__Uint63.les"
]
Packages [ "coq_verified_extraction_ocaml_ffi" ].
