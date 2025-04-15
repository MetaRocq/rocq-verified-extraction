From VerifiedExtraction Require Import Loader.
From Ltac2 Require Import Ltac2.

Inductive value_of {A} : A -> Type := 
  | value_is a : value_of a.
Definition get_value_of {A} {a : A} (c : value_of a) : A := 
  let 'value_is a := c in a.

Lemma value_of_eq {A} {a : A} (c : value_of a) : get_value_of c = a.
Proof. destruct c. reflexivity. Defined. 

(** Runs erasure evaluation only once, in the kernel (if paired with Std.exact). 
  Beware that no check is performed that the cast is correct when using this in a tactic.
  It will be checked at Qed-time only. *)
Ltac2 erase_nocheck c v := 
  let vty := Constr.type c in
  let c := Constr.Unsafe.make (Constr.Unsafe.Cast constr:(@value_is $vty $v) Constr.Cast.erase constr:(@value_of $vty $c)) in
  c.

(** Runs erasure evaluation twice, first to find the value during elaboration, 
    then to check in the kernel *)
Ltac2 erase_compute c := 
  let vty := Constr.type c in
  let c := Constr.pretype preterm:(@value_is $vty _ <<<: @value_of $vty $c) in
  c.

(** Helper to extract the value from an `value_of` term and apply `value_of_eq` to 
  produce an equality. *)
Ltac2 show_value c :=
  let ty := Constr.type c in
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App _ args =>
    let car := Array.get args 0 in
    let computed := Array.get args 1 in
    let term := constr:(@get_value_of $car $computed $c) in
    let cres := eval hnf in $term in
    Std.exact_no_check constr:(value_of_eq $c : $computed = $cres)
  | _ => Control.throw (Invalid_argument None)
  end.

(** Wrappers and notations for the primitives. *)

(** Use `erase_nocheck t v` to get a proof through erasure evaluation that `t` is equal to `v`. 
  The evaluation will happen only when this proof is typechecked by the kernel.
  If `v` is not a value, standard conversion will apply to convert it to `t`'s value found by erased evaluation. *)
Ltac2 erase_nocheck0 t v := show_value (erase_nocheck t v).
Ltac2 Notation "erase_nocheck" t(constr) v(constr) := erase_nocheck0 t v.

(** Use `erase_compute t` to find out the value `v` through erasure evaluation and get a proof that `t` equals `v`. 
  This requires running evaluation twice. I.e. if used in a proof it will run evaluation at the tactic call and again at 
  qed time.
*)
Ltac2 erase_compute0 t := show_value (erase_compute t).
Ltac2 Notation "erase_compute" t(constr) := erase_compute0 t.

(** Just compute the value associated to `t` during elaboration and throw away the proof that it comes from `t`. 
  This runs evaluation only once. *)
Ltac2 erase_forget0 t := 
  let vty := Constr.type t in
  let c := Constr.pretype preterm:(@value_is $vty _ <<<: @value_of $vty $t) in
  match Constr.Unsafe.kind_nocast c with 
  | Constr.Unsafe.App _compute args => Std.exact_no_check (Array.get args 1)
  | _ => Control.throw (Invalid_argument None)
  end.
Ltac2 Notation "erase_forget" t(constr) := erase_forget0 t.

Ltac2 Notation "value_of" c(constr) := show_value c.

(* Tests *)
(*
Definition foo (x : unit) := true.

Definition test := ltac2:(erase_nocheck (foo tt) true).
(* Check test : foo tt = true. *)

Definition testevar := ltac2:(erase_compute (foo tt)).
(* Check testevar : foo tt = true. *)

Definition foo_tt_value := ltac2:(erase_forget (foo tt)).
Check eq_refl : foo_tt_value = true. *)