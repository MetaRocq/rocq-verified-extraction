From VerifiedExtraction Require Import Loader.

Set Verified Extraction Build Directory "_build".

(* Set Debug "verified-extraction". *)

Definition foo := (@eq_refl bool false <<<: (false = negb true)).

From Stdlib Require Import Arith.

Fixpoint fib (n : nat) := 
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n as m) => fib m + fib n
  end.

Time Definition fib2 := Eval compute in fib 2.
Check (@eq_refl nat fib2 <<<: (fib2 = fib 2)).

Time Definition fib23 := Eval compute in fib 23.
(* > 1.5s *)
Time Definition efib23 := (@eq_refl nat fib23 <<<: (fib23 = fib 23)).
(* Runtime is lower (< 1s ) even with compilation + dynlink + reification *)