Require Import Arith List String.
Require Import MetaCoq.VerifiedExtraction.Benchmarks.lib.vs.
Require Import MetaCoq.VerifiedExtraction.Benchmarks.lib.Binom.
Require Import MetaCoq.VerifiedExtraction.Benchmarks.lib.Color.
Require Import MetaCoq.VerifiedExtraction.Benchmarks.lib.sha256.
Require Import MetaCoq.VerifiedExtraction.Benchmarks.lib.tests.

Open Scope string.

Unset Extraction Optimize.
Test Extraction Optimize.

(* The same benchmarks as CertiCoq benchmarks, but slightly modified
   to suspend computations with unit so we can run multiple times *)

Extraction "demo0" demo0.
Extraction "demo1" demo1.
Extraction "demo2" demo2.
Extraction "demo2" demo2.
Extraction "list_sum" list_sum.
(* Modified by hand *)
Extraction "vs_easy" vs_easy.
(* Modified by hand *)
Extraction "vs_hard" vs_hard.
(* Definition binom (_ : unit) := Binom.main. *)
Extraction "binom" binom.
(* Does not typecheck *)
(* Extraction "color" color. *)
Extraction "sha" sha.
Extraction "sha_fast" sha_fast.
