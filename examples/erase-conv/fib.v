From VerifiedExtraction Require Import Extraction.

Set Verified Extraction Build Directory "_build".

(* Set Debug "verified-extraction". *)

Set Verified Extraction Timing.
Set Verified Extraction Format.
Set Verified Extraction Optimize.

(* Definition foo := (@eq_refl bool false <<<: (false = negb true)). *)

From Stdlib Require Import Arith.

Fixpoint fib (n : nat) := 
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n as m) => fib m + fib n
  end.

Time Definition fib2 := Eval compute in fib 2.
(* Check (ltac2:(erase_nocheck (fib 2) fib2)). *)

Definition longtest (x: unit) := 
  let x := fib 30 in match x with 0 => tt | S _ => tt end.
Time Definition fib23 := Eval vm_compute in longtest tt.
(* 0.2s *)
Time Definition efib23 := ltac2:(erase_forget (longtest tt)).
(* 0.3s total, 0.09s runing time *)