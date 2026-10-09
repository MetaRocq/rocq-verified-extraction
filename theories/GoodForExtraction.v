(* Distributed under the terms of the MIT license. *)

(** * A satisfiable PCUIC-level "good for extraction" condition

    [is_good_for_extraction] (Pipeline.v) is a check on the *erased* program.
    This file gives a condition [pcuic_good_for_extraction] on the PCUIC global
    environment (bounds on the number of constructors and constructor
    arguments of every inductive), and proves that, for environments that only
    contain inductive declarations satisfying it,

    - (A) [fo_value_good]: the erasure of every first-order value passes
      [is_good_for_extraction];
    - (B) [app_good]: if the erasures of [f] and [u] pass the check, so does the
      erasure of [tApp f u].

    Everything is generic in the guard implementation and takes the
    normalisation hypothesis as an explicit section variable. *)

From Stdlib Require Import Program ssreflect ssrbool ZArith Lia.
From Equations Require Import Equations.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Utils Require Import bytestring utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICReduction PCUICAstUtils PCUICSN
    PCUICTyping PCUICProgram PCUICFirstorder PCUICEtaExpand.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EImplementBox EPretty Extract.
From MetaRocq.Erasure Require EWellformed EGlobalEnv EProgram.
From MetaRocq Require Import ETransform EConstructorsAsBlocks.
From MetaRocq.ErasurePlugin Require Import Erasure ErasureCorrectness.
From Malfunction Require Import Compile Pipeline.
From Malfunction Require Import ErasureCorrectnessGuard.

Import Transform.Transform.

#[local] Arguments transform : simpl never.

#[local] Existing Instance extraction_checker_flags.

#[local] Existing Instance extraction_normalizing.

(** ** The condition on PCUIC environments *)

(** [cstr_arity] is the field that erasure turns into [EAst.cstr_nargs]; for
    well-formed environments it equals [context_assumptions (cstr_args c)]. *)
Record pcuic_good_for_extraction (Σ : global_env) : Prop := {
  good_ind_blocks : forall kn mind ob, In (kn, InductiveDecl mind) (declarations Σ) ->
      In ob (ind_bodies mind) ->
      blocks_until #|ind_ctors ob| (map cstr_arity (ind_ctors ob)) < 200;
  good_ind_ctors : forall kn mind ob, In (kn, InductiveDecl mind) (declarations Σ) ->
      In ob (ind_bodies mind) -> #|ind_ctors ob| < Z.to_nat Malfunction.Int63.wB;
  good_ind_args : forall kn mind ob c, In (kn, InductiveDecl mind) (declarations Σ) ->
      In ob (ind_bodies mind) -> In c (ind_ctors ob) -> cstr_arity c < int_to_nat array_length
}.

(** A decision procedure, to show that the condition is satisfiable. *)
Definition is_pcuic_good_for_extraction (Σ : global_env) : bool :=
  forallb (fun d => match d.2 with
    | InductiveDecl mind =>
      forallb (fun ob =>
        (blocks_until #|ind_ctors ob| (map cstr_arity (ind_ctors ob)) <? 200) &&
        (Z.of_nat #|ind_ctors ob| <? Malfunction.Int63.wB)%Z &&
        forallb (fun c => Z.of_nat (cstr_arity c) <? array_length_Z)%Z (ind_ctors ob))
        (ind_bodies mind)
    | ConstantDecl _ => true
    end) (declarations Σ).

Lemma is_pcuic_good_for_extraction_sound Σ :
  is_pcuic_good_for_extraction Σ = true -> pcuic_good_for_extraction Σ.
Proof.
  unfold is_pcuic_good_for_extraction. intros H.
  have Hb : forall kn mind ob, In (kn, InductiveDecl mind) (declarations Σ) -> In ob (ind_bodies mind) ->
    (blocks_until #|ind_ctors ob| (map cstr_arity (ind_ctors ob)) <? 200) &&
    (Z.of_nat #|ind_ctors ob| <? Malfunction.Int63.wB)%Z &&
    forallb (fun c => Z.of_nat (cstr_arity c) <? array_length_Z)%Z (ind_ctors ob).
  { intros kn mind ob Hin Hob. eapply forallb_forall in H; [|exact Hin]. cbn in H.
    eapply forallb_forall in H; [|exact Hob]. exact H. }
  constructor.
  - intros kn mind ob Hin Hob. move/andP: (Hb _ _ _ Hin Hob) => [/andP [Hl _] _].
    now apply Nat.ltb_lt.
  - intros kn mind ob Hin Hob. move/andP: (Hb _ _ _ Hin Hob) => [/andP [_ Hl] _].
    apply Z.ltb_lt in Hl. lia.
  - intros kn mind ob c Hin Hob Hc. move/andP: (Hb _ _ _ Hin Hob) => [_ Hl].
    eapply forallb_forall in Hl; [|exact Hc]. apply Z.ltb_lt in Hl.
    unfold array_length_Z in Hl. unfold int_to_nat. lia.
Qed.

(** Sanity check: the condition holds for a small, [bool]-like inductive. *)
Module SanityExample.
  Definition example_ctor (na : ident) : constructor_body :=
    {| cstr_name := na; cstr_args := []; cstr_indices := []; cstr_type := tRel 0; cstr_arity := 0 |}.

  Definition example_body : one_inductive_body :=
    {| ind_name := "bool_like"%bs; ind_indices := []; ind_sort := Sort.type0;
       ind_type := tSort Sort.type0; ind_kelim := IntoAny;
       ind_ctors := [example_ctor "t"%bs; example_ctor "f"%bs]; ind_projs := [];
       ind_relevance := Relevant |}.

  Definition example_mib : mutual_inductive_body :=
    {| ind_finite := Finite; ind_npars := 0; ind_params := []; ind_bodies := [example_body];
       ind_universes := Monomorphic_ctx; ind_variance := None |}.

  Definition example_env : global_env :=
    {| universes := ContextSet.empty;
       declarations := [((MPfile ["Example"%bs], "bool_like"%bs), InductiveDecl example_mib)];
       retroknowledge := Retroknowledge.empty |}.

  Example example_env_check : is_pcuic_good_for_extraction example_env = true.
  Proof. vm_compute. reflexivity. Qed.

  Example example_env_good : pcuic_good_for_extraction example_env.
  Proof. apply is_pcuic_good_for_extraction_sound, example_env_check. Qed.
End SanityExample.

Definition all_inductive (Σ : global_env) :=
  forall kn d, In (kn, d) (declarations Σ) -> exists m, d = InductiveDecl m.

Lemma single_ind_all_inductive univ kn mind retro :
  all_inductive (mk_global_env univ [(kn, InductiveDecl mind)] retro).
Proof.
  intros kn' d [[= _ <-] | []]. now eexists.
Qed.

(** ** Erased environments *)

(** The environment part of [is_good_for_extraction]. *)
Definition is_good_env (fl : EWellformed.EEnvFlags) (Σ : EAst.global_declarations) : bool :=
  check_inductive_bodies (fun ob =>
    let args := map EAst.cstr_nargs (EAst.ind_ctors ob) in
    blocks_until #|args| args <? 200) Σ &&
  check_inductive_bodies (fun ob => Z.of_nat #|EAst.ind_ctors ob| <? Malfunction.Int63.wB)%Z Σ &&
  check_inductive_bodies (fun ob =>
    forallb (fun b => Z.of_nat (EAst.cstr_nargs b) <? array_length_Z)%Z (EAst.ind_ctors ob)) Σ &&
  @check_wf_glob fl Σ.

Lemma is_good_for_extraction_split fl p :
  is_good_for_extraction fl p = is_good_env fl p.1 && @EWellformed.wellformed fl p.1 0 p.2.
Proof. reflexivity. Qed.

Definition erased_mib (m : mutual_inductive_body) : EAst.mutual_inductive_body :=
  ERemoveParams.strip_inductive_decl
    (ErasureFunction.erase_mutual_inductive_body (PCUICExpandLets.trans_minductive_body m)).

Lemma In_mapi_rec {A B} (f : nat -> A -> B) l n x :
  In x (mapi_rec f l n) -> exists k y, In y l /\ x = f k y.
Proof.
  induction l in n |- *; cbn; [easy|].
  intros [<- | H]; [now do 2 eexists; split; [left|]|].
  destruct (IHl _ H) as (k & y & Hy & ->). exists k, y; split; [now right|reflexivity].
Qed.

Lemma erased_mib_bodies m ob' :
  In ob' (EAst.ind_bodies (erased_mib m)) ->
  exists ob, In ob (ind_bodies m) /\
    map EAst.cstr_nargs (EAst.ind_ctors ob') = map cstr_arity (ind_ctors ob).
Proof.
  cbn. intros (ob1 & <- & Hin)%in_map_iff.
  apply In_mapi_rec in Hin as (k & ob & Hob & ->).
  exists ob; split; [exact Hob|].
  cbn. rewrite !map_map. reflexivity.
Qed.

Lemma erased_mib_good Σ kn m ob' :
  pcuic_good_for_extraction Σ ->
  In (kn, InductiveDecl m) (declarations Σ) ->
  In ob' (EAst.ind_bodies (erased_mib m)) ->
  [&& (let args := map EAst.cstr_nargs (EAst.ind_ctors ob') in blocks_until #|args| args <? 200),
      (Z.of_nat #|EAst.ind_ctors ob'| <? Malfunction.Int63.wB)%Z &
      forallb (fun b => Z.of_nat (EAst.cstr_nargs b) <? array_length_Z)%Z (EAst.ind_ctors ob')].
Proof.
  intros Hgood Hin Hob'.
  destruct (erased_mib_bodies _ _ Hob') as (ob & Hob & Heq).
  have Hlen : #|EAst.ind_ctors ob'| = #|ind_ctors ob|.
  { now rewrite -(length_map EAst.cstr_nargs) Heq length_map. }
  apply/and3P; split.
  - cbn. rewrite Heq length_map. apply Nat.leb_le.
    pose proof (good_ind_blocks _ Hgood _ _ _ Hin Hob). lia.
  - rewrite Hlen. apply Z.ltb_lt.
    pose proof (good_ind_ctors _ Hgood _ _ _ Hin Hob). lia.
  - apply forallb_forall. intros b Hb.
    have Hb' : In (EAst.cstr_nargs b) (map cstr_arity (ind_ctors ob)).
    { rewrite -Heq. now apply in_map. }
    apply in_map_iff in Hb' as (c & Hcb & Hc). apply Z.ltb_lt. rewrite -Hcb.
    pose proof (good_ind_args _ Hgood _ _ _ _ Hin Hob Hc).
    unfold int_to_nat in *. unfold array_length_Z. lia.
Qed.

Lemma wf_glob_In_lookup {efl : EWellformed.EEnvFlags} Σ kn d :
  @EWellformed.wf_glob efl Σ -> In (kn, d) Σ -> EGlobalEnv.lookup_env Σ kn = Some d.
Proof.
  induction 1 as [|kn' d' Σ HΣ IH Hd Hfresh]; cbn; [easy|].
  intros [[= -> ->] | Hin].
  - now rewrite eqb_refl.
  - destruct (eqb_spec kn kn'); [|now apply IH].
    subst. eapply Forall_forall in Hfresh; [|exact Hin]. cbn in Hfresh. congruence.
Qed.

Lemma erased_env_shape (Σ : global_env) (Σ_t : EAst.global_declarations) {efl : EWellformed.EEnvFlags} :
  @EWellformed.wf_glob efl Σ_t ->
  all_inductive Σ ->
  (forall kn d, EGlobalEnv.lookup_env Σ_t kn = Some d ->
    exists decl', lookup_global (PCUICExpandLets.trans_global_decls (declarations Σ)) kn = Some decl' /\
      erase_decl_equal (fun d => ERemoveParams.strip_inductive_decl (ErasureFunction.erase_mutual_inductive_body d)) d decl') ->
  forall kn d, In (kn, d) Σ_t ->
    exists m, In (kn, InductiveDecl m) (declarations Σ) /\ d = EAst.InductiveDecl (erased_mib m).
Proof.
  intros Hwf Hind Hlook kn d Hin.
  apply (wf_glob_In_lookup _ _ _ Hwf) in Hin.
  destruct (Hlook _ _ Hin) as (decl' & Hl & Heq).
  apply lookup_global_Some_if_In in Hl.
  unfold PCUICExpandLets.trans_global_decls in Hl.
  apply in_map_iff in Hl as ([kn0 d0] & [= <- <-] & Hin0).
  destruct (Hind _ _ Hin0) as [m ->].
  exists m; split; [exact Hin0|].
  destruct d; cbn in Heq; [easy|]. now subst.
Qed.

Lemma check_wf_glob_transfer {efl efl' : EWellformed.EEnvFlags} Σ :
  @EWellformed.has_cstr_params efl = @EWellformed.has_cstr_params efl' ->
  @EWellformed.wf_glob efl Σ ->
  (forall kn d, In (kn, d) Σ -> exists m, d = EAst.InductiveDecl m) ->
  @check_wf_glob efl' Σ.
Proof.
  intros Hfl. induction 1 as [|kn d Σ HΣ IH Hd Hfresh]; cbn; [easy|].
  intros Hind. destruct (Hind kn d (or_introl eq_refl)) as [m ->].
  apply/andP; split; [apply/andP; split|].
  - apply IH. intros kn' d' Hin. eapply Hind. now right.
  - cbn in Hd |- *. unfold EWellformed.wf_minductive in Hd |- *. now rewrite -Hfl.
  - apply forallb_forall. intros x Hx. eapply Forall_forall in Hfresh; [|exact Hx].
    destruct (eqb_spec x.1 kn); cbn; congruence.
Qed.

Lemma erased_env_core (Σ : global_env) (Σ_t : EAst.global_declarations) {efl : EWellformed.EEnvFlags} :
  @EWellformed.has_cstr_params efl = false ->
  @EWellformed.wf_glob efl Σ_t ->
  all_inductive Σ ->
  pcuic_good_for_extraction Σ ->
  (forall kn d, EGlobalEnv.lookup_env Σ_t kn = Some d ->
    exists decl', lookup_global (PCUICExpandLets.trans_global_decls (declarations Σ)) kn = Some decl' /\
      erase_decl_equal (fun d => ERemoveParams.strip_inductive_decl (ErasureFunction.erase_mutual_inductive_body d)) d decl') ->
  is_good_env extraction_env_flags_mlf Σ_t = true.
Proof.
  intros Hfl Hwf Hind Hgood Hlook.
  pose proof (erased_env_shape Σ Σ_t Hwf Hind Hlook) as Hshape.
  have Hbodies : forall kn d, In (kn, d) Σ_t ->
    match d with
    | EAst.InductiveDecl mb => forall ob, In ob (EAst.ind_bodies mb) ->
       [&& (let args := map EAst.cstr_nargs (EAst.ind_ctors ob) in blocks_until #|args| args <? 200),
           (Z.of_nat #|EAst.ind_ctors ob| <? Malfunction.Int63.wB)%Z &
           forallb (fun b => Z.of_nat (EAst.cstr_nargs b) <? array_length_Z)%Z (EAst.ind_ctors ob)]
    | EAst.ConstantDecl _ => True
    end.
  { intros kn d Hin. destruct (Hshape _ _ Hin) as (m & Hinm & ->).
    intros ob Hob. eapply erased_mib_good; eauto. }
  unfold is_good_env, check_inductive_bodies.
  apply/andP; split; [apply/andP; split; [apply/andP; split|]|].
  1-3: apply forallb_forall; intros [kn d] Hin; specialize (Hbodies _ _ Hin); cbn;
    destruct d as [|mb]; [easy|];
    apply forallb_forall; intros ob Hob; move/and3P: (Hbodies ob Hob) => [? ? ?]; assumption.
  eapply (check_wf_glob_transfer (efl := efl)); [now rewrite Hfl|exact Hwf|].
  intros kn d Hin. destruct (Hshape _ _ Hin) as (m & _ & ->). now eexists.
Qed.

(** ** First-order values and applications *)

Lemma firstorder_evalue_block_wellformed Σ t :
  firstorder_evalue_block Σ t -> @EWellformed.wellformed extraction_env_flags_mlf Σ 0 t.
Proof.
  revert t. apply firstorder_evalue_block_elim.
  intros i n args Hl _ IH.
  have Hc : EWellformed.isSome (EGlobalEnv.lookup_constructor Σ i n).
  { move: Hl. unfold EGlobalEnv.lookup_constructor_pars_args.
    destruct EGlobalEnv.lookup_constructor; cbn; congruence. }
  cbn -[EGlobalEnv.lookup_constructor_pars_args EGlobalEnv.lookup_constructor].
  rewrite Hc Hl /=. apply/andP; split.
  - apply/eqb_spec. reflexivity.
  - apply forallb_forall. intros x Hx. eapply Forall_forall in IH; eauto.
Qed.

Lemma fo_good_core p :
  is_good_env extraction_env_flags_mlf p.1 = true ->
  firstorder_evalue_block p.1 p.2 ->
  is_good_for_extraction extraction_env_flags_mlf p = true.
Proof.
  intros He Hfo. rewrite is_good_for_extraction_split He /=.
  now apply firstorder_evalue_block_wellformed.
Qed.

Lemma app_good_core papp pf pu :
  is_good_env extraction_env_flags_mlf papp.1 = true ->
  is_good_for_extraction extraction_env_flags_mlf pf = true ->
  is_good_for_extraction extraction_env_flags_mlf pu = true ->
  EGlobalEnv.extends pf.1 papp.1 ->
  EGlobalEnv.extends pu.1 papp.1 ->
  papp = (papp.1, EAst.tApp pf.2 pu.2) ->
  is_good_for_extraction extraction_env_flags_mlf papp = true.
Proof.
  destruct papp as [Σa ta]; cbn [fst snd].
  intros He Hf Hu Ef Eu [= ->].
  rewrite is_good_for_extraction_split in Hf. move/andP: Hf => [_ Hf].
  rewrite is_good_for_extraction_split in Hu. move/andP: Hu => [_ Hu].
  have Hwf : @EWellformed.wf_glob extraction_env_flags_mlf Σa.
  { apply check_wf_glob_sound. move/andP: He => [_ ?]. assumption. }
  rewrite is_good_for_extraction_split He /=.
  rewrite (EWellformed.extends_wellformed Hwf Ef _ _ Hf).
  now rewrite (EWellformed.extends_wellformed Hwf Eu _ _ Hu).
Qed.

Section GoodForExtraction.
  Context {guard : abstract_guard_impl}.

  Variable Normalisation : forall Σ0 : global_env_ext, wf_ext Σ0 -> NormalizationIn Σ0.

  Lemma pre_erasure_inv (Σ : global_env_ext_map) t
    (pr : pre (verified_erasure_pipeline default_erasure_config) (Σ, t)) :
    ∥ wf_ext Σ ∥ /\ (exists T, ∥ Σ ;;; [] |- t : T ∥) /\
    expanded_global_env Σ.1 /\ expanded Σ.1 [] t.
  Proof.
    destruct pr as [[[wf [T ty]]] [[e1 e2] _]].
    split; [now constructor|]. split; [exists T; now constructor|]. now split.
  Qed.

  Lemma post_erasure_wf_glob p :
    post (verified_erasure_pipeline default_erasure_config) p ->
    exists efl, @EWellformed.has_cstr_params efl = false /\ @EWellformed.wf_glob efl p.1.
  Proof.
    cbn. intros [H _]. eexists; split; [|exact H]. reflexivity.
  Qed.

  (** The environment of every erased program passes the environment checks. *)
  Lemma erased_env_good (Σ : global_env_ext_map) t
    (Hind : all_inductive Σ.1) (Hgood : pcuic_good_for_extraction Σ.1)
    (pr : pre (verified_erasure_pipeline default_erasure_config) (Σ, t)) :
    is_good_env extraction_env_flags_mlf (transform (verified_erasure_pipeline default_erasure_config) (Σ, t) pr).1 = true.
  Proof.
    destruct (pre_erasure_inv _ _ pr) as [[HΣ] [[T typing] [expΣ expt]]].
    destruct (post_erasure_wf_glob _ (correctness (verified_erasure_pipeline default_erasure_config) (Σ, t) pr))
      as [efl [Hfl Hwf]].
    apply (erased_env_core Σ.1 _ Hfl Hwf Hind Hgood).
    intros kn d Hl.
    exact (verified_erasure_pipeline_lookup_env_in_gen (guard := guard) Σ t T HΣ expΣ expt typing
      Normalisation default_erasure_config pr kn d (has_rel := eq_refl) (has_box := eq_refl) Hl).
  Qed.

  (** Lemma (A): the erasure of a first-order value is good for extraction. *)
  Lemma fo_value_good (Σ : global_env_ext_map)
    (Hind : all_inductive Σ.1) (Hgood : pcuic_good_for_extraction Σ.1)
    (axfree : PCUICClassification.axiom_free Σ)
    v i u args (typing : ∥ Σ ;;; [] |- v : mkApps (tInd i u) args ∥)
    (fo : firstorder_ind Σ (firstorder_env Σ) i)
    (Hval : firstorder_value Σ [] v) :
    forall pr, is_good_for_extraction extraction_env_flags_mlf
      (transform (verified_erasure_pipeline default_erasure_config) (Σ, v) pr) = true.
  Proof.
    intros pr.
    destruct (pre_erasure_inv _ _ pr) as [[HΣ] [_ [expΣ expv]]].
    assert (Heval : ∥ PCUICWcbvEval.eval Σ v v ∥).
    { destruct typing as [typing']. sq.
      eapply PCUICValidity.validity in typing' as Hv.
      destruct Hv as [_ [? [HA _]]].
      eapply PCUICValidity.inversion_mkApps in HA as (A & HA & _).
      eapply PCUICInversion.inversion_Ind in HA as (mdecl & idecl & _ & HA & _); eauto.
      eapply (PCUICNormalization.wcbv_standardization_fst (normalization := Normalisation Σ HΣ)); eauto.
      - instantiate (1 := mdecl). destruct HΣ.
        unshelve eapply declared_inductive_to_gen in HA; eauto.
      - intros [t' ht]. eapply PCUICNormalization.firstorder_value_irred; eauto. }
    pose proof (verified_erasure_pipeline_firstorder_evalue_block_gen (guard := guard) Σ HΣ expΣ v expv axfree
      v i u args Normalisation typing fo Heval default_erasure_config pr) as Hfo.
    rewrite (v_t_spec_gen (guard := guard) Σ HΣ expΣ v expv axfree
      v i u args Normalisation typing fo Heval default_erasure_config pr) in Hfo.
    apply fo_good_core; [|exact Hfo].
    now apply erased_env_good.
  Qed.

  (** Lemma (B): applications of good programs are good. *)
  Lemma app_good (Σ : global_env_ext_map)
    (Hind : all_inductive Σ.1) (Hgood : pcuic_good_for_extraction Σ.1) f u
    (Hgood_f : forall pr, is_good_for_extraction extraction_env_flags_mlf
      (transform (verified_erasure_pipeline default_erasure_config) (Σ, f) pr) = true)
    (Hgood_u : forall pr, is_good_for_extraction extraction_env_flags_mlf
      (transform (verified_erasure_pipeline default_erasure_config) (Σ, u) pr) = true)
    (Hner : ∥ Extract.nisErasable Σ [] (tApp f u) ∥) (Hexp : expanded Σ.1 [] f) :
    forall pr, is_good_for_extraction extraction_env_flags_mlf
      (transform (verified_erasure_pipeline default_erasure_config) (Σ, tApp f u) pr) = true.
  Proof.
    intros pr.
    destruct (erasure_pipeline_extends_app (guard := guard) Σ f u pr default_erasure_config Hner Hexp)
      as (pre' & pre'' & [Ef Eu] & Happ).
    exact (app_good_core _ _ _ (erased_env_good Σ (tApp f u) Hind Hgood pr)
      (Hgood_f pre') (Hgood_u pre'') Ef Eu Happ).
  Qed.

  (** Specialisations to environments with a single inductive declaration
      (the setting of Firstorder.v). *)
  Section single.
    Variables (univ : ContextSet.t) (retro : Retroknowledge.t) (univ_decl : universes_decl)
      (kn : kername) (mind : mutual_inductive_body).

    Let Σ0 := mk_global_env univ [(kn, InductiveDecl mind)] retro.
    Let Σ : global_env_ext_map := (build_global_env_map Σ0, univ_decl).

    Lemma fo_value_good_single (Hgood : pcuic_good_for_extraction Σ0)
      (axfree : PCUICClassification.axiom_free Σ)
      v i u args (typing : ∥ Σ ;;; [] |- v : mkApps (tInd i u) args ∥)
      (fo : firstorder_ind Σ (firstorder_env Σ) i)
      (Hval : firstorder_value Σ [] v) :
      forall pr, is_good_for_extraction extraction_env_flags_mlf
        (transform (verified_erasure_pipeline default_erasure_config) (Σ, v) pr) = true.
    Proof.
      exact (fo_value_good Σ (single_ind_all_inductive univ kn mind retro) Hgood axfree v i u args typing fo Hval).
    Qed.

    Lemma app_good_single (Hgood : pcuic_good_for_extraction Σ0) f u
      (Hgood_f : forall pr, is_good_for_extraction extraction_env_flags_mlf
        (transform (verified_erasure_pipeline default_erasure_config) (Σ, f) pr) = true)
      (Hgood_u : forall pr, is_good_for_extraction extraction_env_flags_mlf
        (transform (verified_erasure_pipeline default_erasure_config) (Σ, u) pr) = true)
      (Hner : ∥ Extract.nisErasable Σ [] (tApp f u) ∥) (Hexp : expanded Σ.1 [] f) :
      forall pr, is_good_for_extraction extraction_env_flags_mlf
        (transform (verified_erasure_pipeline default_erasure_config) (Σ, tApp f u) pr) = true.
    Proof.
      exact (app_good Σ (single_ind_all_inductive univ kn mind retro) Hgood f u Hgood_f Hgood_u Hner Hexp).
    Qed.
  End single.

End GoodForExtraction.

Print Assumptions fo_value_good.
Print Assumptions app_good.
Print Assumptions fo_value_good_single.
Print Assumptions app_good_single.
Print Assumptions SanityExample.example_env_good.
