From Malfunction.Plugin Require Import Loader CoqMsgFFI.
From VerifiedExtractionBootstrap Require Import BootstrapPrimInt63 BootstrapPrimFloat BootstrapPrimArray.
From Malfunction Require Import Pipeline.

Set Verified Extraction Build Directory "_build".

(* Malfunction.Plugin.Extract binds all primitives to OCaml externals *)
Set Warnings "-primitive-turned-into-axiom".

Verified Extract Inductives [ bool => "bool" [ 1 0 ] ].

(* MetaCoq Run Print mli compile_malfunction_gen. *)
Verified Extraction -fmt compile_malfunction_gen "compile_malfunction.mlf".
