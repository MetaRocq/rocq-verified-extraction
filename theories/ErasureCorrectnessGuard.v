(* Guard-generic copies of lemmas from MetaRocq.ErasurePlugin.ErasureCorrectness.

   The lemmas below are verbatim copies (modulo the changes marked CHANGED) of lemmas of
   MetaRocq's ErasurePlugin/ErasureCorrectness.v. In MetaRocq they were proved in sections
   without a guard-checker context, so the implicit [abstract_guard_impl] argument of the
   erasure pipeline was resolved to the global instance [fake_guard_impl], making the lemmas
   depend on the axiom [fake_guard_impl_properties] (and some on [fake_normalization]).
   Here they are proved inside sections with [Context {guard : abstract_guard_impl}], so that
   they hold for every guard implementation, and normalisation is taken from hypotheses.
   Names and explicit-argument order are kept identical, so importing this file after
   [MetaRocq.ErasurePlugin.ErasureCorrectness] shadows the MetaRocq versions. *)

(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Utils Require Import bytestring utils.
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaRocq.PCUIC Require Import PCUICNormal.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureCorrectness EPretty Extract EProgram EConstructorsAsBlocks.
From MetaRocq.Erasure Require Import EWcbvEvalNamed ErasureFunction ErasureFunctionProperties.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
Import EProgram PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

(* This is the total erasure function +
  let-expansion of constructor arguments and case branches +
  shrinking of the global environment dependencies +
  the optimization that removes all pattern-matches on propositions. *)

Import Common.Transform.Transform.

#[local] Obligation Tactic := program_simpl.

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

Import EWcbvEval.
From MetaRocq.ErasurePlugin Require Import ErasureCorrectness.

Import EEnvMap.GlobalContextMap.

Section GenericObseq.
  Context {guard : abstract_guard_impl}.

Lemma obseq_lambdabox (Σt Σ'v : EProgram.eprogram_env) econf pr pr' p' v' :
  EGlobalEnv.extends Σ'v.1 Σt.1 ->
  obseq (verified_lambdabox_pipeline econf) Σt pr p' Σ'v.2 v' ->
  (transform (verified_lambdabox_pipeline econf) Σ'v pr').2 = v'.
Proof.
  intros ext obseq.
  destruct Σt as [Σ t], Σ'v as [Σ' v].
  pose proof verified_lambdabox_pipeline_extends'.
  red in H.
  assert (pr'' : pre (verified_lambdabox_pipeline econf) (Σ, v)).
  { clear -pr pr' ext. destruct pr as [[] ?], pr' as [[] ?].
    split. red; cbn. split => //.
    eapply EWellformed.extends_wellformed; tea.
    split. apply H1. cbn. destruct H4; cbn in *.
    eapply EEtaExpandedFix.isEtaExp_expanded.
    eapply EEtaExpandedFix.isEtaExp_extends; tea.
    now eapply EEtaExpandedFix.expanded_isEtaExp. }
  destruct (H _ _ _ pr' pr'') as [ext' ->].
  split => //.
  clear H.
  move: obseq.
  unfold verified_lambdabox_pipeline.
  set(ecf := econf) in *.
  destruct econf as [? ? ? ? ? ?].
  destruct inlining.
  - unfold inlining_transformation.
    cbn [optional_self_transform inlining ecf] in *.
    rewrite obseq_compose_assoc.
    rewrite transform_compose_assoc.
    repeat destruct_compose; cbn [transform] in *.
    cbn [transform forget_inlining_info_transformation] in *.
    cbn [transform inline_transformation] in *.
    cbn [transform rebuild_wf_env_transform] in *.
    cbn [transform constructors_as_blocks_transformation] in *.
    cbn [transform inline_projections_optimization] in *.
    cbn [transform remove_match_on_box_trans] in *.
    cbn [transform remove_params_optimization] in *.
    cbn [transform guarded_to_unguarded_fix] in *.
    intros ? ? ? ? ? ? ? ? ?.
    unfold run, time.
    cbn [obseq compose forget_inlining_info_transformation] in *.
    cbn [obseq compose inline_transformation] in *.
    cbn [obseq compose constructors_as_blocks_transformation] in *.
    cbn [obseq run compose rebuild_wf_env_transform] in *.
    cbn [obseq compose inline_projections_optimization] in *.
    cbn [obseq compose remove_match_on_box_trans] in *.
    cbn [obseq compose remove_params_optimization] in *.
    cbn [obseq compose guarded_to_unguarded_fix] in *.
    intros obs.
    decompose [ex and prod] obs. clear obs. subst.
    unfold run, time.
    cbn [transform inline_transformation] in *.
    unfold EInlining.inline_program.
    EInlining.destruct_inline_env.
    unfold EConstructorsAsBlocks.transform_blocks_program. cbn [snd]. do 2 f_equal.
    {
      unfold EInlining.inlined_program_inlinings.
      repeat destruct_compose.
      intros.
      cbn [transform inline_transformation] in *.
      unfold EInlining.inline_program.
      EInlining.destruct_inline_env.
      cbn [transform constructors_as_blocks_transformation] in *.
      cbn [transform rebuild_wf_env_transform] in *.
      cbn [transform inline_projections_optimization] in *.
      cbn [transform remove_match_on_box_trans] in *.
      cbn [transform remove_params_optimization] in *.
      cbn [transform guarded_to_unguarded_fix] in *.
      unfold EConstructorsAsBlocks.transform_blocks_program.
      cbn [fst snd].
      do 3 f_equal.
      eapply rebuild_wf_env_irr.
      unfold EInlineProjections.optimize_program. cbn [fst snd].
      f_equal.
      eapply rebuild_wf_env_irr.
      unfold EOptimizePropDiscr.remove_match_on_box_program. cbn [fst snd].
      f_equal.
      now eapply rebuild_wf_env_irr.
    }
    repeat destruct_compose.
    intros.
    cbn [transform rebuild_wf_env_transform] in *.
    cbn [transform constructors_as_blocks_transformation] in *.
    cbn [transform inline_projections_optimization] in *.
    cbn [transform remove_match_on_box_trans] in *.
    cbn [transform remove_params_optimization] in *.
    cbn [transform guarded_to_unguarded_fix] in *.
    eapply rebuild_wf_env_irr.
    unfold EInlineProjections.optimize_program. cbn [fst snd].
    f_equal.
    eapply rebuild_wf_env_irr.
    unfold EOptimizePropDiscr.remove_match_on_box_program. cbn [fst snd].
    f_equal.
    now eapply rebuild_wf_env_irr.
  - cbn [optional_self_transform inlining ecf] in *.
    repeat destruct_compose; cbn [transform] in *.
    cbn [transform rebuild_wf_env_transform] in *.
    cbn [transform constructors_as_blocks_transformation] in *.
    cbn [transform inline_projections_optimization] in *.
    cbn [transform remove_match_on_box_trans] in *.
    cbn [transform remove_params_optimization] in *.
    cbn [transform guarded_to_unguarded_fix] in *.
    intros ? ? ? ? ? ? ? ?.
    unfold run, time.
    cbn [obseq compose constructors_as_blocks_transformation] in *.
    cbn [obseq run compose rebuild_wf_env_transform] in *.
    cbn [obseq compose inline_projections_optimization] in *.
    cbn [obseq compose remove_match_on_box_trans] in *.
    cbn [obseq compose remove_params_optimization] in *.
    cbn [obseq compose guarded_to_unguarded_fix] in *.
    intros obs.
    decompose [ex and prod] obs. clear obs. subst.
    unfold run, time.
    unfold EConstructorsAsBlocks.transform_blocks_program. cbn [snd]. f_equal.
    repeat destruct_compose.
    intros.
    cbn [transform rebuild_wf_env_transform] in *.
    cbn [transform constructors_as_blocks_transformation] in *.
    cbn [transform inline_projections_optimization] in *.
    cbn [transform remove_match_on_box_trans] in *.
    cbn [transform remove_params_optimization] in *.
    cbn [transform guarded_to_unguarded_fix] in *.
    eapply rebuild_wf_env_irr.
    unfold EInlineProjections.optimize_program. cbn [fst snd].
    f_equal.
    eapply rebuild_wf_env_irr.
    unfold EOptimizePropDiscr.remove_match_on_box_program. cbn [fst snd].
    f_equal.
    now eapply rebuild_wf_env_irr.
Qed.

End GenericObseq.

From MetaRocq.Erasure Require Import Erasure Extract ErasureFunction.
From MetaRocq.PCUIC Require Import PCUICTyping.
From Equations Require Import Equations.

Import EWcbvEval.
Arguments erase_global_deps _ _ _ _ _ : clear implicits.
Arguments erase_global_deps_fast _ _ _ _ _ _ : clear implicits.

Section GenericFO.
  Context {guard : abstract_guard_impl}.

Section PCUICProof.
  Import PCUICAst.PCUICEnvironment.

  Lemma erase_tranform_firstorder (wfl := default_wcbv_flags)
    {p : Transform.program global_env_ext_map PCUICAst.term} {pr v i u args}
    {normalization_in : PCUICSN.NormalizationIn p.1} :
    forall (wt : p.1 ;;; [] |- p.2 : PCUICAst.mkApps (PCUICAst.tInd i u) args),
    axiom_free p.1 ->
    @PCUICFirstorder.firstorder_ind p.1 (PCUICFirstorder.firstorder_env p.1) i ->
    PCUICWcbvEval.eval p.1 p.2 v ->
    forall ep, transform erase_transform p pr = ep ->
      erase_preserves_inductives p.1 ep.1 /\
      ∥ EWcbvEval.eval ep.1 ep.2 (compile_value_erase v []) ∥ /\
      firstorder_evalue ep.1 (compile_value_erase v []).
  Proof.
    destruct p as [Σ t]; cbn.
    intros ht ax fo ev [Σe te]; cbn.
    unfold erase_program, erase_pcuic_program.
    set (obl := ETransform.erase_pcuic_program_obligation_6 _ _ _ _ _ _).
    move: obl.
    rewrite /erase_global_fast.
    set (prf0 := fun (Σ0 : global_env) => _).
    set (prf1 := fun (Σ0 : global_env_ext) => _).
    set (prf2 := fun (Σ0 : global_env_ext) => _).
    set (prf3 := fun (Σ0 : global_env) => _).
    set (prf4 := fun n (H : n < _) => _).
    set (gext := PCUICWfEnv.abstract_make_wf_env_ext _ _ _).
    set (et := erase _ _ _ _ _).
    set (g := build_wf_env_from_env _ _).
    assert (hprefix: forall Σ0 : global_env, PCUICWfEnv.abstract_env_rel g Σ0 -> declarations Σ0 = declarations g).
    { intros Σ' eq; cbn in eq. rewrite eq; reflexivity. }
    destruct (@erase_global_deps_fast_erase_global_deps (EAstUtils.term_global_deps et) optimized_abstract_env_impl g
      (declarations Σ) prf4 prf3 hprefix) as [nin' eq].
    cbn [fst snd].
    rewrite eq.
    set (eg := erase_global_deps _ _ _ _ _ _).
    intros obl.
    epose proof (@erase_correct_strong optimized_abstract_env_impl g Σ.2 prf0 t v i u args _ _ hprefix prf1 prf2 Σ eq_refl ax ht fo).
    pose proof (proj1 pr) as [[]].
    forward H. eapply PCUICClassification.wcbveval_red; tea.
    assert (PCUICFirstorder.firstorder_value Σ [] v).
    { eapply PCUICFirstorder.firstorder_value_spec; tea. apply w. constructor.
      eapply PCUICClassification.subject_reduction_eval; tea.
      eapply PCUICWcbvEval.eval_to_value; tea. }
    forward H.
    { intros [v' redv]. eapply PCUICNormalization.firstorder_value_irred; tea. }
    destruct H as [wt' [ev' fo']].
    assert (erase optimized_abstract_env_impl (PCUICWfEnv.abstract_make_wf_env_ext (X_type:=optimized_abstract_env_impl) g Σ.2 prf0) [] v wt' =
      compile_value_erase v []).
    { clear -H0.
      clearbody prf0 prf1.
      destruct pr as [].
      destruct s as [[]].
      epose proof (erases_erase (X_type := optimized_abstract_env_impl) wt' _ eq_refl).
      eapply erases_firstorder' in H; eauto. }
    rewrite H in ev', fo'.
    intros [=]; subst te Σe.
    split => //.
    cbn. subst eg.
    intros kn decl decl' hl hl'.
    eapply lookup_env_in_erase_global_deps in hl as [decl'' [hl eq']].
    rewrite /lookup_env hl in hl'. now noconf hl'.
    eapply wf_fresh_globals, w.
  Qed.
End PCUICProof.
Lemma erase_transform_fo_gen (p : pcuic_program) pr :
  PCUICFirstorder.firstorder_value p.1 [] p.2 ->
  forall ep, transform erase_transform p pr = ep ->
  ep.2 = compile_value_erase p.2 [].
Proof.
  destruct p as [Σ t]. cbn.
  intros hev ep <-. move: hev pr.
  unfold erase_program, erase_pcuic_program; cbn -[erase PCUICWfEnv.abstract_make_wf_env_ext].
  intros fo pr.
  set (prf0 := fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _).
  set (prf1 := fun (Σ0 : PCUICAst.PCUICEnvironment.global_env_ext) => _).
  clearbody prf0 prf1.
  destruct pr as [].
  destruct s as [[]].
  epose proof (erases_erase (X_type := optimized_abstract_env_impl) prf1 _ eq_refl).
  eapply erases_firstorder' in H; eauto.
Qed.

Lemma erase_transform_fo (p : pcuic_program) pr :
  PCUICFirstorder.firstorder_value p.1 [] p.2 ->
  transform erase_transform p pr = ((transform erase_transform p pr).1, compile_value_erase p.2 []).
Proof.
  intros fo.
  set (tr := transform _ _ _).
  change tr with (tr.1, tr.2). f_equal.
  eapply erase_transform_fo_gen; tea. reflexivity.
Qed.

End GenericFO.

Import MetaRocq.Common.Transform.
From Stdlib Require Import Morphisms.

Section ErasureFunction.
  Import PCUICAst PCUICAst.PCUICEnvironment PCUIC.PCUICConversion PCUICArities PCUICSpine PCUICOnFreeVars PCUICWellScopedCumulativity.
  Import EAst EAstUtils EWcbvEval EArities.

  (* CHANGED: explicit [NormalizationIn] hypothesis instead of the global [fake_normalization]. *)
  Lemma pcuic_function_value (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) {Σ : global_env_ext} {f na A B}
    (wfΣ : wf_ext Σ) (axfree : axiom_free Σ) (wf : Σ ;;; [] |- f : PCUICAst.tProd na A B)
    (Normalisation : PCUICSN.NormalizationIn Σ) : { v & PCUICWcbvEval.eval Σ f v }.
  Proof.
    eapply (PCUICNormalization.wcbv_normalization wfΣ axfree wf).
  Qed.

  (* CHANGED: normalisation is obtained from the precondition [pr]. *)
  Lemma erase_function_to_function (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map) f v' na A B
    (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr :
    axiom_free Σ ->
    ∥ nisErasable Σ [] f ∥ ->
    let (Σ', f') := transform erase_transform (Σ, f) pr in
    eval Σ' f' v' -> isFunction v' = true.
  Proof.
    intros axfree nise.
    pose proof (proj1 (proj2 (proj2 pr))) as nin.
    destruct pr as [[]]. destruct wf.
    epose proof (pcuic_function_value w.1 axfree X (nin w.1)) as [v hv].
    eapply erase_function; tea. now sq.
  Qed.

End ErasureFunction.

Import EWellformed.
Import EAstUtils.
Import EInlining.

Section GenericLambdaBox.
  Context {guard : abstract_guard_impl}.

Lemma lambdabox_pres_fo econf :
  exists compile_value, ETransformPresFO.t (verified_lambdabox_pipeline econf) fo_evalue_map (fun p => firstorder_evalue_block p.1 p.2) compile_value /\
    forall p pr fo, (compile_value p pr fo).2 = compile_evalue_box (ERemoveParams.strip p.1 p.2) [].
Proof.
  Opaque ERemoveParams.strip.
  destruct econf as [? ? ? []].
  - eexists.
    split.
    unfold verified_lambdabox_pipeline.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:intros p pr fo; unfold ETransformPresFO.compose_compile_fo_value; cbn; f_equal.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    eapply remove_match_on_box_pres => //.
    destruct p as [Γ t].
    unfold inline_program.
    destruct_inline_env.
    unfold fo_evalue_map in fo.
    unfold ETransformPresFO.compose_compile_fo_value; cbn -[ERemoveParams.strip ERemoveParams.strip_env inline_env] in *.
    inversion fo; subst.
    assert (forall inlining t l, List.map (inline inlining) l = l -> inline inlining (compile_evalue_box t l) = compile_evalue_box t l) as heq.
    { clear.
      intros env t l heq.
      induction t in l, heq |- *; simpl; try easy.
      now rewrite IHt1 //= IHt2. }
    now rewrite heq.
  - eexists.
    split.
    unfold verified_lambdabox_pipeline.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:intros p pr fo; unfold ETransformPresFO.compose_compile_fo_value; cbn; f_equal.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    2:unfold ETransformPresFO.compose_compile_fo_value; cbn.
    unshelve eapply ETransformPresFO.compose; tc. shelve.
    eapply remove_match_on_box_pres => //.
    destruct p as [Γ t].
    now unfold ETransformPresFO.compose_compile_fo_value; cbn -[ERemoveParams.strip ERemoveParams.strip_env inline_env] in *.
Qed.

#[local] Instance lambdabox_pres_app econf :
  ETransformPresAppLam.t (verified_lambdabox_pipeline econf) is_eta_fix_app_map (fun _ => True).
Proof.
  unfold verified_lambdabox_pipeline.
  do 6 (unshelve eapply ETransformPresAppLam.compose; [shelve| |tc]).
  2:{ eapply remove_match_on_box_pres_app => //. }
  do 2 (unshelve eapply ETransformPresAppLam.compose; [shelve| |tc]).
  tc.
Qed.

Lemma transform_lambda_box_firstorder (Σer : EEnvMap.GlobalContextMap.t) econf p pre :
  firstorder_evalue Σer p ->
  (transform (verified_lambdabox_pipeline econf) (Σer, p) pre).2 = (compile_evalue_box (ERemoveParams.strip Σer p) []).
Proof.
  intros fo.
  destruct (lambdabox_pres_fo econf) as [fn [tr hfn]].
  rewrite (ETransformPresFO.transform_fo _ _ _ _ (t:=tr)).
  now rewrite hfn.
Qed.

Lemma transform_lambda_box_eta_app (Σer : EEnvMap.GlobalContextMap.t) t u pre econf :
  EEtaExpandedFix.isEtaExp Σer [] t ->
  exists pre' pre'',
  transform (verified_lambdabox_pipeline econf) (Σer, EAst.tApp t u) pre =
  ((transform (verified_lambdabox_pipeline econf) (Σer, EAst.tApp t u) pre).1,
    EAst.tApp (transform (verified_lambdabox_pipeline econf) (Σer, t) pre').2
      (transform (verified_lambdabox_pipeline econf) (Σer, u) pre'').2).
Proof.
  intros etat.
  epose proof (ETransformPresAppLam.transform_app (verified_lambdabox_pipeline econf) is_eta_fix_app_map (fun _ => True) Σer t u pre etat).
  exact H.
Qed.

Lemma transform_lambdabox_pres_term p p' pre pre' econf :
  extends_eprogram_env p p' ->
  (transform (verified_lambdabox_pipeline econf) p pre).2 =
  (transform (verified_lambdabox_pipeline econf) p' pre').2.
Proof.
  intros hext. epose proof (verified_lambdabox_pipeline_extends' _ p p' pre pre' hext).
  apply H.
Qed.

Lemma transform_erase_pres_term (p p' : program global_env_ext_map PCUICAst.term) pre pre' :
  extends_global_env p.1 p'.1 ->
  p.2 = p'.2 ->
  (transform erase_transform p pre).2 =
  (transform erase_transform p' pre').2.
Proof.
  destruct p as [ctx t], p' as [ctx' t']. cbn.
  intros hg heq; subst t'. eapply ErasureFunction.erase_irrel_global_env.
  eapply equiv_env_inter_hlookup.
  intros ? ?; cbn. intros -> ->. cbn. now eapply extends_global_env_equiv_env.
Qed.

End GenericLambdaBox.

#[local] Existing Instance lambdabox_pres_app.

Section GenericPCUICErase.
  Context {guard : abstract_guard_impl}.

Section PCUICErase.
  Import PCUICAst PCUICAstUtils PCUICEtaExpand PCUICWfEnv.

  Definition lift_wfext (Σ : global_env_ext_map) (wfΣ : ∥ wf_ext Σ ∥) :
    let wfe := build_wf_env_from_env Σ.1 (map_squash (wf_ext_wf Σ) wfΣ) in
    (forall Σ' : global_env, Σ' ∼ wfe -> ∥ wf_ext (Σ', Σ.2) ∥).
  Proof.
    intros wfe; cbn; intros ? ->. apply wfΣ.
  Qed.

  (* (forall Σ : global_env, Σ ∼ X -> ∥ wf_ext (Σ, univs) ∥) *)
  Lemma snd_erase_pcuic_program {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program) (nin : wf_ext p.1 -> PCUICSN.NormalizationIn p.1)
    (nin' : wf_ext p.1 -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p.1)
    (wfΣ : ∥ wf_ext p.1 ∥) (wt : ∥ ∑ T : term, p.1;;; [] |- p.2 : T ∥) :
    let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ) in
    let Xext := abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl) wfe p.1.2 (lift_wfext p.1 wfΣ) in
    exists wt' nin'', (@erase_pcuic_program guard_impl p nin nin' wfΣ wt).2 = erase optimized_abstract_env_impl (normalization_in := nin'') Xext [] p.2 wt'.
  Proof.
    unfold erase_pcuic_program.
    cbn -[erase]. do 2 eexists. eapply ErasureFunction.erase_irrel_global_env.
    red. cbn. intros. split => //.
    Unshelve. intros ? ->. destruct wt as [[T wt]]. now econstructor.
    destruct wfΣ.
    intros ? ? ->. now eapply nin.
  Qed.

  Definition wt'_erase_pcuic_program {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program)
    (wfΣ : ∥ wf_ext p.1 ∥) (wt : ∥ ∑ T : term, p.1;;; [] |- p.2 : T ∥) :
    let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ) in
    let Xext := abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl) wfe p.1.2 (lift_wfext p.1 wfΣ) in
    forall Σ : global_env_ext, Σ ∼_ext abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl) wfe p.1.2 (fun (Σ0 : global_env) (H : Σ0 ∼ wfe) => ETransform.erase_pcuic_program_obligation_1 guard_impl p wfΣ Σ0 H) -> welltyped Σ [] p.2.
    intros.
    refine ((let 'sq s as wt' := wt return (wt' = wt -> welltyped Σ [] p.2) in
      let '(T; ty) as s0 := s return (sq s0 = wt -> welltyped Σ [] p.2) in
          fun _ : sq (T; ty) = wt => iswelltyped (eq_rect (p.1 : global_env_ext) (fun Σ0 : global_env_ext => Σ0;;; [] |- p.2 : T) ty Σ (ETransform.erase_pcuic_program_obligation_3 guard_impl p wfΣ Σ H)))
         eq_refl).
  Defined.

  Definition erase_nin {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program) (nin : wf_ext p.1 -> PCUICSN.NormalizationIn p.1)
    (wfΣ : ∥ wf_ext p.1 ∥) :=
    fun (Σ : global_env_ext) (H : wf_ext Σ) (H0 : Σ = abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl) (build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ)) p.1.2 (fun (Σ0 : global_env) (H0 : Σ0 = p.1.1) => ETransform.erase_pcuic_program_obligation_1 guard_impl p wfΣ Σ0 H0)) =>
    ETransform.erase_pcuic_program_obligation_2 guard_impl p nin wfΣ Σ H H0 .

  Lemma fst_erase_pcuic_program {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program) (nin : wf_ext p.1 -> PCUICSN.NormalizationIn p.1)
    (nin' : wf_ext p.1 -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p.1)
    (wfΣ : ∥ wf_ext p.1 ∥) (wt : ∥ ∑ T : term, p.1;;; [] |- p.2 : T ∥) :
    let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ) in
    let Xext := abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl (guard := guard_impl)) wfe p.1.2 (lift_wfext p.1 wfΣ) in
    let nin'' := erase_nin p nin wfΣ in
    let er := erase optimized_abstract_env_impl (normalization_in := nin'') Xext [] p.2 (wt'_erase_pcuic_program p wfΣ wt) in
    exists hprefix nin2 hfr,
    (@erase_pcuic_program guard_impl p nin nin' wfΣ wt).1 =
    make (erase_global_deps optimized_abstract_env_impl (term_global_deps er) wfe (declarations p.1) nin2 hprefix).1 hfr.
  Proof.
    intros.
    unfold erase_pcuic_program. rewrite -/wfe -/nin' -/Xext.
    cbn -[erase abstract_make_wf_env_ext].
    set (er' := erase _ _ _ _ _).
    assert (er = er').
    { subst er er'.
      eapply ErasureFunction.erase_irrel_global_env.
      red. cbn. intros. split => //. }
    rewrite /erase_global_fast.
    set(prf := fun (n : nat) => _).
    set(prf' := fun (Σ : global_env) => _).
    unshelve eexists. intros ? ->; reflexivity.
    epose proof (@erase_global_deps_fast_erase_global_deps (term_global_deps er') optimized_abstract_env_impl wfe (declarations p.1) _ _ _) as [nin2 eq].
    exists nin2.
    set(prf'' := fun (Σ : global_env) => _).
    set(prf''' := ETransform.erase_pcuic_program_obligation_6 _ _ _ _ _ _).
    cbn zeta in prf'''. unfold erase_global_fast in prf'''.
    clearbody prf'''.
    revert prf'''. rewrite eq -H. intros prf'''.
    exists prf'''. f_equal.
    Unshelve. apply prf'.
  Qed.

  Lemma fst_erase_pcuic_program' {no : PCUICSN.normalizing_flags} {guard_impl : abstract_guard_impl} (p : pcuic_program) (nin : wf_ext p.1 -> PCUICSN.NormalizationIn p.1)
    (nin' : wf_ext p.1 -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p.1)
    (wfΣ : ∥ wf_ext p.1 ∥) (wt : ∥ ∑ T : term, p.1;;; [] |- p.2 : T ∥) :
    expanded p.1 [] p.2 ->
    let wfe := build_wf_env_from_env p.1.1 (map_squash (wf_ext_wf p.1) wfΣ) in
    let Xext := abstract_make_wf_env_ext (X_type := optimized_abstract_env_impl (guard := guard_impl)) wfe p.1.2 (lift_wfext p.1 wfΣ) in
    forall wt' nin'',
    let er := erase optimized_abstract_env_impl (normalization_in := nin'') Xext [] p.2 wt' in
    EEtaExpandedFix.expanded (@erase_pcuic_program guard_impl p nin nin' wfΣ wt).1 [] er.
  Proof.
    intros.
    unfold erase_pcuic_program. rewrite -/wfe -/nin' -/Xext.
    cbn -[erase abstract_make_wf_env_ext].
    set (er' := erase _ _ _ _ _).
    assert (er = er') as <-.
    { subst er er'.
      eapply ErasureFunction.erase_irrel_global_env.
      red. cbn. intros. split => //. }
    rewrite /erase_global_fast.
    epose proof erase_global_deps_fast_erase_global_deps as [nin2 eq].
    erewrite eq. clear eq.
    eapply expanded_erase; revgoals; tea. cbn. reflexivity.
    Unshelve. cbn; intros ? ->; reflexivity.
  Qed.

  Lemma erase_eta_app (Σ : global_env_ext_map) t u pre :
    ~ ∥ isErasable Σ [] (tApp t u) ∥ ->
    PCUICEtaExpand.expanded Σ [] t ->
    exists pre' pre'',
    let trapp := transform erase_transform (Σ, PCUICAst.tApp t u) pre in
    let trt := transform erase_transform (Σ, t) pre' in
    let tru := transform erase_transform (Σ, u) pre'' in
    EEtaExpandedFix.isEtaExp trt.1 [] trt.2 /\
    EGlobalEnv.extends trt.1 trapp.1 /\
    EGlobalEnv.extends tru.1 trapp.1 /\
    trapp = (trapp.1, EAst.tApp trt.2 tru.2).
  Proof.
    intros er etat.
    unshelve eexists.
    { destruct pre as [[] []]. cbn in *. split => //. 2:split => //.
      destruct X. split. split => //. destruct s as [appty tyapp].
      eapply PCUICInversion.inversion_App in tyapp as [na [A [B [hp [hu hcum]]]]]. now eexists.
      cbn. apply w.
      destruct H; split => //. }
    unshelve eexists.
    { destruct pre as [[] []]. cbn in *. split => //. 2:split => //.
      destruct X. split. split => //. destruct s as [appty tyapp].
      eapply PCUICInversion.inversion_App in tyapp as [na [A [B [hp [hu hcum]]]]]. now eexists.
      cbn. apply w.
      destruct H; split => //. cbn. cbn in H1. now eapply expanded_tApp_arg in H1. }
    unfold transform, erase_transform. cbn -[erase_program].
    unfold erase_program.
    set (prf := map_squash _ _); clearbody prf.
    set (prf0 := map_squash _ _); clearbody prf0.
    set (prf1 := map_squash _ _); clearbody prf1.
    set (prf2 := map_squash _ _); clearbody prf2.
    set (prf3 := map_squash _ _); clearbody prf3.
    set (prf4 := map_squash _ _); clearbody prf4.
    set (erp := erase_pcuic_program (_, tApp _ _) _ _).
    destruct erp eqn:heq. f_equal. subst erp.
    pose proof (f_equal snd heq). cbn -[erase_pcuic_program] in H.
    rewrite -{}H.
    match goal with
    [ |- context [ @erase_pcuic_program ?guard (?Σ, tApp ?t ?u) ?nin ?nin' ?prf ?prf' ] ] =>
    destruct (snd_erase_pcuic_program (Σ, tApp t u) nin nin' prf prf') as [wt' [nin'' ->]]
    end. cbn [fst snd].
    rewrite (erase_mkApps _ _ [u]).
    { cbn; intros ? ->. destruct prf4 as [[? hu]]. repeat constructor. cbn in hu. eexists. exact hu. }
    intros.
    cbn [E.mkApps erase_terms].
    match goal with
    [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
    destruct (snd_erase_pcuic_program p nin nin' prf prf') as [wt'' [nin''' ->]]
    end.
    split; [|split; [|split]].
    - cbn [fst snd]. eapply EEtaExpandedFix.expanded_isEtaExp.
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        epose proof (fst_erase_pcuic_program' p nin nin' prf prf' etat)
      end.
      eapply H.
    - clear -er heq. apply (f_equal fst) in heq. cbn [fst] in heq. rewrite -heq. clear -er.
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        set (ninprf := nin); clearbody ninprf;
        set (ninprf' := nin'); clearbody ninprf';
        epose proof (fst_erase_pcuic_program p ninprf ninprf' prf prf')
      end.
      destruct H as [hpref [ning [hfr ->]]].
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        set (ninprf0 := nin); clearbody ninprf0;
        set (ninprf0' := nin'); clearbody ninprf0';
        epose proof (fst_erase_pcuic_program p ninprf0 ninprf0' prf prf')
      end.
      destruct H as [hpref' [ning' [hfr' ->]]].
      cbn -[erase_global_deps term_global_deps erase abstract_make_wf_env_ext build_wf_env_from_env].
      rewrite !erase_global_deps_erase_global.
      (* assert (wfg : wf_glob (erase_global (build_wf_env_from_env Σ.1 (map_squash (wf_ext_wf Σ) prf))). *)
      erewrite -> @filter_deps_filter.
      2:{ eapply erase_global_wf_glob. }
      erewrite -> @filter_deps_filter.
      2:{ eapply erase_global_wf_glob. }
      assert (prf = prf1) by apply proof_irrelevance.
      assert (hpref = hpref') by apply proof_irrelevance. subst prf1 hpref'.
      assert (ning = ning') by apply proof_irrelevance. subst ning'.
      eapply extends_filter_impl.
      2:{ eapply erase_global_wf_glob. }
      intros x. unfold flip.
      clear -er.
      set (env := abstract_make_wf_env_ext _ _ _).
      match goal with
      [ |- context [ @erase ?X_type ?X ?nin ?G (tApp _ _) ?wt ] ] =>
        unshelve epose proof (@erase_mkApps X_type X nin G t [u] wt (wt'_erase_pcuic_program (Σ, t) prf prf0))
      end.
      assert (hargs : forall Σ : global_env_ext, Σ ∼_ext env -> ∥ All (welltyped Σ []) [u] ∥).
      { cbn; intros ? ->. do 2 constructor; auto. destruct prf. destruct prf2 as [[T HT]]. eapply PCUICInversion.inversion_App in HT as HT'.
        destruct HT' as [na [A [B [Hp []]]]]. now eexists. eapply w. }
      specialize (H hargs).
      forward H by repeat constructor.
      forward H. { cbn; intros ? ->. exact er. }
      rewrite H. rewrite term_global_deps_mkApps. intros hin. eapply KernameSet.mem_spec.
      rewrite global_deps_union. eapply KernameSet.union_spec. left.
      eapply KernameSet.mem_spec in hin. clear -hin.
      set (er0 := @erase _ _ _ _ _ _) in hin.
      set (er1 := @erase _ _ _ _ _ _).
      assert (er0 = er1). { unfold er0, er1. eapply ErasureFunction.erase_irrel_global_env. intro. cbn. intros -> ? ->; cbn; intuition eauto. }
      now rewrite -H.
    - clear -prf0 er heq etat. apply (f_equal fst) in heq. cbn [fst] in heq. rewrite -heq. clear -er etat prf0.
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        set (ninprf := nin); clearbody ninprf;
        set (ninprf' := nin'); clearbody ninprf';
        epose proof (fst_erase_pcuic_program p ninprf ninprf' prf prf')
      end.
      destruct H as [hpref [ning [hfr ->]]].
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
        set (ninprf0 := nin); clearbody ninprf0;
        set (ninprf0' := nin'); clearbody ninprf0';
        epose proof (fst_erase_pcuic_program p ninprf0 ninprf0' prf prf')
      end.
      destruct H as [hpref' [ning' [hfr' ->]]].
      cbn -[erase_global_deps term_global_deps erase abstract_make_wf_env_ext build_wf_env_from_env].
      rewrite !erase_global_deps_erase_global.
      (* assert (wfg : wf_glob (erase_global (build_wf_env_from_env Σ.1 (map_squash (wf_ext_wf Σ) prf))). *)
      erewrite -> @filter_deps_filter.
      2:{ eapply erase_global_wf_glob. }
      erewrite -> @filter_deps_filter.
      2:{ eapply erase_global_wf_glob. }
      assert (prf3 = prf1) by apply proof_irrelevance.
      assert (hpref = hpref') by apply proof_irrelevance. subst prf1 hpref'.
      assert (ning = ning') by apply proof_irrelevance. subst ning'.
      eapply extends_filter_impl.
      2:{ eapply erase_global_wf_glob. }
      intros x. unfold flip.
      clear -er prf0.
      set (env := abstract_make_wf_env_ext _ _ _).
      match goal with
      [ |- context [ @erase ?X_type ?X ?nin ?G (tApp _ _) ?wt ] ] =>
        unshelve epose proof (@erase_mkApps X_type X nin G t [u] wt (wt'_erase_pcuic_program (Σ, t) prf3 prf0))
      end.
      assert (hargs : forall Σ : global_env_ext, Σ ∼_ext env -> ∥ All (welltyped Σ []) [u] ∥).
      { cbn; intros ? ->. do 2 constructor; auto. destruct prf4 as [[T HT]]. eexists; eapply HT. }
      specialize (H hargs).
      forward H by repeat constructor.
      forward H. { cbn; intros ? ->. exact er. }
      rewrite H. rewrite term_global_deps_mkApps. intros hin. eapply KernameSet.mem_spec.
      rewrite global_deps_union. eapply KernameSet.union_spec. right. cbn [erase_terms].
      eapply KernameSet.mem_spec in hin. clear -hin.
      set (er0 := @erase _ _ _ _ _ _) in hin.
      set (er1 := @erase _ _ _ _ _ _).
      assert (er0 = er1). { unfold er0, er1. eapply ErasureFunction.erase_irrel_global_env. intro. cbn. intros -> ? ->; cbn; intuition eauto. }
      rewrite -H. cbn. rewrite global_deps_union. eapply KernameSet.union_spec. now left.
    - f_equal. f_equal. eapply ErasureFunction.erase_irrel_global_env. red. cbn. intros; split => //.
      match goal with
      [ |- context [ @erase_pcuic_program ?guard ?p ?nin ?nin' ?prf ?prf' ] ] =>
      destruct (snd_erase_pcuic_program p nin nin' prf prf') as [wt''' [nin'''' ->]]
      end. eapply ErasureFunction.erase_irrel_global_env. red. cbn. intros; split => //.
      - intros. constructor.
      - now cbn; intros ? ->.
      - cbn; intros ? ->. destruct prf0 as [[? wtt]]. eexists; apply wtt.
  Qed.

  Import PCUICWellScopedCumulativity PCUICFirstorder PCUICNormalization PCUICReduction PCUIC.PCUICConversion PCUICPrincipality.
  Import PCUICExpandLets PCUICExpandLetsCorrectness.
  Import PCUICOnFreeVars PCUICSigmaCalculus.

  Lemma transform_erasure_pipeline_function'
    (wfl := default_wcbv_flags)
    {guard_impl : abstract_guard_impl}
    (cf:=config.extraction_checker_flags) (Σ:global_env_ext_map)
    {f na A B}
    (wf : ∥ Σ ;;; [] |- f : PCUICAst.tProd na A B ∥) pr econf :
    axiom_free Σ ->
    ∥ nisErasable Σ [] f ∥ ->
    let tr := transform (verified_erasure_pipeline econf) (Σ, f) pr in
    exists v, ∥ eval (wfl := extraction_wcbv_flags) tr.1 tr.2 v ∥ /\ isFunction v = true.
  Proof.
    intros axfree nise.
    unfold verified_erasure_pipeline.
    rewrite -!transform_compose_assoc.
    pose proof (expand_lets_function Σ (fun p : global_env_ext_map =>
    (wf_ext p -> PCUICSN.NormalizationIn p) /\
    (wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p)) f na A B wf pr).
    destruct_compose. intros pre.
    set (trexp := transform (pcuic_expand_lets_transform _) _ _) in *.
    eapply (PCUICExpandLetsCorrectness.trans_axiom_free Σ) in axfree.
    have nise' : ∥ nisErasable trexp.1 [] trexp.2 ∥.
    destruct pr as [[[]] ?], nise. sq; now eapply nisErasable_lets.
    change (trans_global_env _) with (global_env_ext_map_global_env_ext trexp.1).1 in axfree.
    clearbody trexp. clear nise pr wf Σ f. destruct trexp as [Σ f].
    (* CHANGED: normalisation is taken from the precondition [pre]. *)
    pose proof pre as pre'; destruct pre' as [[[wf _]] [_ [nin _]]].
    pose proof (map_squash (fun X => pcuic_function_value wf axfree X (nin wf)) H) as [[v ev]].
    epose proof (Transform.preservation erase_transform).
    specialize (H0 _ v pre (sq ev)).
    revert H0.
    destruct_compose. intros pre' htr.
    destruct htr as [v'' [ev' _]].
    epose proof (erase_function_to_function _ f v'' _ _ _ H pre axfree nise').
    set (tre := transform erase_transform _ _) in *. clearbody tre.
    cbn -[transform obseq].
    red in ev'. destruct ev'.
    epose proof (Transform.preservation (verified_lambdabox_pipeline econf)).
    destruct tre as [Σ' f'].
    specialize (H2 _ v'' pre' (sq H1)) as [finalv [[evfinal] obseq]].
    exists finalv.
    split. now sq.
    have prev : Transform.pre (verified_lambdabox_pipeline econf) (Σ', v'').
    { clear -wfl pre' H1. cbn in H1.
      destruct pre' as [[] []]. split; split => //=.
      eapply EWcbvEval.eval_wellformed; eauto.
      eapply EEtaExpandedFix.isEtaExp_expanded.
      eapply (@EEtaExpandedFix.eval_etaexp wfl); eauto.
      now eapply EEtaExpandedFix.expanded_global_env_isEtaExp_env.
      now eapply EEtaExpandedFix.expanded_isEtaExp. }
    specialize (H0 H1).
    eapply (obseq_lambdabox (Σ', f') (Σ', v'') econf) in obseq.
    epose proof (ETransformPresAppLam.transform_lam _ _ _ (t0 := (lambdabox_pres_app econf)) (Σ', v'') prev H0).
    rewrite -obseq. exact H2. cbn. red; tauto.
  Qed.

  Lemma expand_lets_transform_env K p p' pre pre' :
    p.1 = p'.1 ->
    (transform (pcuic_expand_lets_transform K) p pre).1 =
    (transform (pcuic_expand_lets_transform K) p' pre').1.
  Proof.
    unfold transform, pcuic_expand_lets_transform. cbn. now intros ->.
  Qed.

  Opaque erase_transform.

  Lemma extends_eq Σ Σ0 Σ' : EGlobalEnv.extends Σ Σ' -> Σ = Σ0 -> EGlobalEnv.extends Σ0 Σ'.
  Proof. now intros ext ->. Qed.

  Lemma erasure_pipeline_extends_app (Σ : global_env_ext_map) t u pre econf :
    ∥ nisErasable Σ [] (tApp t u) ∥ ->
    PCUICEtaExpand.expanded Σ [] t ->
    exists pre' pre'',
    let trapp := transform (verified_erasure_pipeline econf) (Σ, PCUICAst.tApp t u) pre in
    let trt := transform (verified_erasure_pipeline econf) (Σ, t) pre' in
    let tru := transform (verified_erasure_pipeline econf) (Σ, u) pre'' in
    (EGlobalEnv.extends trt.1 trapp.1 /\ EGlobalEnv.extends tru.1 trapp.1) /\
    trapp = (trapp.1, EAst.tApp trt.2 tru.2).
  Proof.
    intros ner exp.
    unfold verified_erasure_pipeline.
    destruct_compose.
    set (K:= (fun p : global_env_ext_map => (wf_ext p -> PCUICSN.NormalizationIn p) /\ (wf_ext p -> PCUICWeakeningEnvSN.normalizationInAdjustUniversesIn p))).
    intros H.
    assert (ner' : ~ ∥ isErasable Σ [] (tApp t u) ∥).
    { destruct ner as [ner]. destruct pre, s. eapply nisErasable_spec in ner => //. eapply w. }
    destruct (expand_lets_eta_app _ _ _ K pre ner' exp) as [pre' [pre'' eq]].
    exists pre', pre''.
    set (tr := transform _ _ _).
    destruct tr eqn:heq. cbn -[transform].
    replace t0 with tr.2. assert (heq_env:tr.1=g) by now rewrite heq. subst tr.
    2:{ now rewrite heq. }
    clear heq. revert H.
    destruct_compose_no_clear. rewrite eq. intros pre3 eq2 pre4.
    epose proof (erase_eta_app _ _ _ pre3) as H0.
    pose proof (correctness (pcuic_expand_lets_transform K) (Σ, tApp t u) pre).
    destruct H as [[wtapp] [expapp Kapp]].
    pose proof (correctness (pcuic_expand_lets_transform K) (Σ, t) pre').
    destruct H as [[wtt] [expt Kt]].
    forward H0.
    { clear -wtapp ner eq. apply (f_equal snd) in eq. cbn [snd] in eq. rewrite -eq.
      destruct pre as [[wtp] rest].
      destruct ner as [ner]. eapply (nisErasable_lets (Σ, tApp t u)) in ner.
      eapply nisErasable_spec in ner => //. cbn.
      apply wtapp. apply wtp. }
    forward H0 by apply expt.
    destruct H0 as [pre'0 [pre''0 [eta [extapp [extapp' heq]]]]].
    split.
    { rewrite <- heq_env. cbn -[transform].
      pose proof (EProgram.TransformExt.preserves_obs _ _ _ (t:=verified_lambdabox_pipeline_extends' econf)).
      unfold extends_eprogram in H.
      split.
      { repeat (destruct_compose; intros). eapply verified_lambdabox_pipeline_extends.
        repeat (destruct_compose; intros). cbn - [transform].
        generalize dependent pre3. rewrite <- eq.
        cbn [transform pcuic_expand_lets_transform expand_lets_program].
        unfold expand_lets_program. cbn [fst snd].
        intros pre3. cbn in pre3. intros <-. intros.
        assert (pre'0 = H1). apply proof_irrelevance. subst H1.
        exact extapp. }
      { repeat (destruct_compose; intros). eapply verified_lambdabox_pipeline_extends.
        repeat (destruct_compose; intros). cbn - [transform].
        generalize dependent pre3. rewrite <- eq.
        cbn [transform pcuic_expand_lets_transform expand_lets_program].
        unfold expand_lets_program. cbn [fst snd].
        intros pre3. cbn in pre3. intros <-. intros.
        assert (pre''0 = H1). apply proof_irrelevance. subst H1.
        exact extapp'. } }
    set (tr := transform _ _ _).
    destruct tr eqn:heqtr. cbn -[transform]. f_equal.
    replace t1 with tr.2. subst tr.
    2:{ now rewrite heqtr; cbn. }
    clear heqtr.
    move: pre4.
    rewrite heq. intros h.
    epose proof (transform_lambda_box_eta_app _ _ _ h econf).
    forward H. { cbn [fst snd].
      clear -eq eta extapp. revert pre3 extapp.
      rewrite -eq. pose proof (correctness _ _ pre'0).
      destruct H as [? []]. cbn [fst snd] in eta |- *. revert pre'0 H H0 H1 eta. rewrite eq.
      intros. cbn -[transform] in H1. cbn -[transform].
      eapply EEtaExpandedFix.expanded_isEtaExp in H1.
      eapply EEtaExpandedFix.isEtaExp_extends; tea.
      pose proof (correctness _ _ pre3). apply H2. }
    destruct H as [prelam [prelam' eqlam]]. rewrite eqlam.
    rewrite snd_pair. clear eqlam.
    destruct_compose_no_clear.
    intros hlt heqlt. symmetry.
    apply f_equal2.
    eapply transform_lambdabox_pres_term.
    split. rewrite fst_pair.
    { destruct_compose_no_clear. intros H eq'. clear -extapp.
      eapply extends_eq; tea. do 2 f_equal. clear extapp.
      change (transform (pcuic_expand_lets_transform K) (Σ, tApp t u) pre).1 with
        (transform (pcuic_expand_lets_transform K) (Σ, t) pre').1 in pre'0 |- *.
      revert pre'0.
      rewrite -surjective_pairing. intros pre'0. f_equal. apply proof_irrelevance. }
    rewrite snd_pair.
    destruct_compose_no_clear. intros ? ?.
    eapply transform_erase_pres_term.
    rewrite fst_pair.
    { red. cbn. split => //. } reflexivity.
    (* CHANGED: explicit guard (otherwise unification hangs). *)
    eapply (transform_lambdabox_pres_term (guard := guard) _ _ _ _ econf).
    split. rewrite fst_pair.
    { unfold run, time. destruct_compose_no_clear. intros H eq'. clear -extapp'.
      assert (pre''0 = H). apply proof_irrelevance. subst H. apply extapp'. }
    cbn [snd run]. unfold run, time.
    destruct_compose_no_clear. intros ? ?.
    eapply transform_erase_pres_term. cbn [fst].
    { red. cbn. split => //. } reflexivity.
  Qed.

Transparent erase_transform.

End PCUICErase.

End GenericPCUICErase.

Arguments PCUICFirstorder.firstorder_ind _ _ : clear implicits.

Section GenericPipeline.
  Context {guard : abstract_guard_impl}.

Section pipeline_cond.

  Variable Σ : global_env_ext_map.
  Variable t : PCUICAst.term.
  Variable T : PCUICAst.term.

  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.

  Variable typing : ∥PCUICTyping.typing Σ [] t T∥.

  Variable Normalisation : (forall Σ, wf_ext Σ -> PCUICSN.NormalizationIn Σ).
  Variable econf : erasure_configuration.

  Lemma precond : pre (verified_erasure_pipeline econf) (Σ, t).
  Proof.
    hnf. destruct typing. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. eauto.
    - intros. red. intros. now eapply Normalisation.
  Qed.

  Variable v : PCUICAst.term.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Lemma precond2 : pre (verified_erasure_pipeline econf) (Σ, v).
  Proof.
    cbn. destruct typing, Heval. repeat eapply conj; sq; cbn; eauto.
    - red. cbn. split; eauto.
      eexists.
      eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply (PCUICClassification.wcbveval_red (Σ := Σ)) in X; tea.
      eapply PCUICEtaExpand.expanded_red in X; tea. apply HΣ.
      intros ? ?; rewrite nth_error_nil => //.
    - cbn. intros wf ? ? ? ? ? ?. now eapply Normalisation.
  Qed.

  Let Σ_t := (transform (verified_erasure_pipeline econf) (Σ, t) precond).1.
  Let t_t := (transform (verified_erasure_pipeline econf) (Σ, t) precond).2.
  Let Σ_v := (transform (verified_erasure_pipeline econf) (Σ, v) precond2).1.
  Let v_t := compile_value_box (PCUICExpandLets.trans_global_env Σ) v [].

  Lemma lookup_inline (efl := (EConstructorsAsBlocks.switch_cstr_as_blocks
(EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params all_env_flags)))) p pr kn :
    EGlobalEnv.lookup_env (transform (optional_self_transform (Erasure.inlining econf) (inlining_transformation eq_refl econf)) p pr).1 kn =
    option_map (if econf.(Erasure.inlining) then inline_global_decl (inline_env econf.(inlined_constants) p.1).2 else fun x => x) (EGlobalEnv.lookup_env p.1 kn).
  Proof.
    clear -efl.
    destruct econf as [? ? ? []]; cbn.
    - unfold inline_program; destruct_inline_env; cbn. eapply EInlining.lookup_env_inline.
      apply pr.
    - now rewrite option_map_id.
  Qed.

  Opaque compose.
  Lemma verified_erasure_pipeline_lookup_env_in kn decl (efl := ERemoveParams.switch_no_params all_env_flags)
    {has_rel : has_tRel} {has_box : has_tBox} :
    EGlobalEnv.lookup_env Σ_t kn = Some decl ->
   exists decl',
    PCUICAst.PCUICEnvironment.lookup_global (PCUICExpandLets.trans_global_decls
    (PCUICAst.PCUICEnvironment.declarations Σ.1)) kn = Some decl'
    /\  erase_decl_equal (fun decl => ERemoveParams.strip_inductive_decl (erase_mutual_inductive_body decl))
           decl decl'.
  Proof.
  unfold Σ_t, verified_erasure_pipeline.
  repeat rewrite -transform_compose_assoc.
  destruct_compose; intro. cbn.
  destruct_compose; intro. cbn.
  set (erase_program _ _).
  unfold verified_lambdabox_pipeline.
  repeat rewrite -transform_compose_assoc.
  repeat (destruct_compose; intro).
  set (transform (guarded_to_unguarded_fix _) _ _) as t1.
  set (transform (remove_params_optimization _ _ _) _ _) as t2.
  set (transform remove_match_on_box_trans _ _) as t3.
  set (transform (rebuild_wf_env_transform true false) _ _) as t4 at 2.
  set (transform (inline_projections_optimization _ _) _ _) as t5.
  set (transform (rebuild_wf_env_transform true false) _ _) as t6.
  set (transform constructors_as_blocks_transformation _ _) as t7.
  rewrite lookup_inline.
  (* set (if _ then inline_global_decl _ else _) as t8. *)
  subst t7.
  set (eenv := inline_env _ _). clearbody eenv.
  unfold transform at 1. cbn -[transform].
  rewrite EConstructorsAsBlocks.lookup_env_transform_blocks.
  set (EConstructorsAsBlocks.transform_blocks_decl _).
  subst t6.
  unfold transform at 1. cbn -[transform].
  subst t5.
  unfold transform at 1. cbn -[transform].
  erewrite EInlineProjections.lookup_env_optimize.
  2: { apply H5. }
  set (EInlineProjections.optimize_decl _).
  subst t4.
  unfold transform at 1. cbn -[transform].
  subst t3.
  unfold transform at 1. cbn -[transform].
  erewrite EOptimizePropDiscr.lookup_env_remove_match_on_box.
  2: { apply H3. }
  set (EOptimizePropDiscr.remove_match_on_box_decl _).
  subst t2.
  unfold transform at 1. cbn -[transform].
  subst t1.
  unfold transform at 1. cbn -[transform].
  erewrite ERemoveParams.lookup_env_strip.
  set (ERemoveParams.strip_decl _).
  unfold transform at 1. cbn -[transform].
  rewrite erase_global_deps_fast_spec.
  2: { cbn. intros ? He. rewrite He. eauto. }
  intro.
  set (EAstUtils.term_global_deps _).
  set (build_wf_env_from_env _ _).
  set (EGlobalEnv.lookup_env _ _).
  case_eq o. 2: { intros ?. inversion 1. }
  intros decl' Heq.
  unshelve epose proof
    (Hlookup := lookup_env_in_erase_global_deps optimized_abstract_env_impl w t0
    _ kn _ Hyp0 decl' _ Heq).
  { epose proof (wf_fresh_globals _ HΣ). clear - H9.
    revert H9. cbn. set (Σ.1). induction 1; econstructor; eauto.
    cbn. clear -H. induction H; econstructor; eauto. }
  destruct Hlookup as [decl'' [? ?]]. exists decl''; split ; eauto.
  cbn in H11. inversion H11.
  set (b := Erasure.inlining econf) in H13 |- *. clearbody b.
  now destruct b, decl' , decl''.
  Qed.

End pipeline_cond.


Section pipeline_theorem.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.

  Variable t : PCUICAst.term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.
  Variable axfree : axiom_free Σ.
  Variable v : PCUICAst.term.

  Variable i : Kernames.inductive.
  Variable u : Universes.Instance.t.
  Variable args : list PCUICAst.term.

  Variable Normalisation :  (forall Σ, wf_ext Σ -> PCUICSN.NormalizationIn Σ).

  Variable typing : ∥PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args)∥.

  Variable fo : @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Lemma fo_v : PCUICFirstorder.firstorder_value Σ [] v.
  Proof.
    destruct typing, Heval. sq.
    eapply PCUICFirstorder.firstorder_value_spec; eauto.
    - eapply PCUICClassification.subject_reduction_eval; eauto.
    - eapply PCUICWcbvEval.eval_to_value; eauto.
  Qed.

  Variable econf : erasure_configuration.

  Let Σ_t := (transform (verified_erasure_pipeline econf) (Σ, t) (precond _ _ _ _ expΣ expt typing _ econf)).1.
  Let t_t := (transform (verified_erasure_pipeline econf) (Σ, t) (precond _ _ _ _ expΣ expt typing _ econf)).2.
  Let Σ_v := (transform (verified_erasure_pipeline econf) (Σ, v) (precond2 _ _ _ _ expΣ expt typing _ econf _ Heval)).1.
  Let v_t := compile_value_box (PCUICExpandLets.trans_global_env Σ) v [].

  Lemma verified_erasure_pipeline_extends (efl := ERemoveParams.switch_no_params all_env_flags)
   {has_rel : has_tRel} {has_box : has_tBox} :
   EGlobalEnv.extends Σ_v Σ_t.
  Proof.
  unfold Σ_v, Σ_t. unfold verified_erasure_pipeline.
  repeat (destruct_compose; intro). destruct typing as [typing'], Heval.
  cbn [transform compose pcuic_expand_lets_transform] in *.
  unfold run, time.
  cbn [transform erase_transform] in *.
  set (erase_program _ _). set (erase_program _ _).
  eapply verified_lambdabox_pipeline_extends.
  eapply extends_erase_pcuic_program; eauto.
    unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (cf := extraction_checker_flags) (Σ := (Σ.1, Σ.2))).
    { now eapply PCUICExpandLetsCorrectness.trans_wf. }
    { clear -HΣ typing'. now eapply PCUICClosedTyp.subject_closed in typing'. }
    assumption.
    now eapply PCUICExpandLetsCorrectness.trans_axiom_free.
    pose proof (PCUICExpandLetsCorrectness.expand_lets_sound typing').
    rewrite PCUICExpandLetsCorrectness.trans_mkApps in X. eapply X.
    move: fo. clear.
    { rewrite /PCUICFirstorder.firstorder_ind /=.
      rewrite PCUICExpandLetsCorrectness.trans_lookup.
      destruct PCUICAst.PCUICEnvironment.lookup_env => //.
      destruct g => //=.
      eapply PCUICExpandLetsCorrectness.trans_firstorder_mutind.
      eapply PCUICExpandLetsCorrectness.trans_firstorder_env. }
  Qed.


  Lemma v_t_spec : v_t = (transform (verified_erasure_pipeline econf) (Σ, v) (precond2 _ _ _ _ expΣ expt typing _ econf _ Heval)).2.
  Proof.
    unfold v_t. generalize fo_v. set (pre := precond2 _ _ _ _ _ _ _ _ _ _ _) in *. clearbody pre.
    intros hv.
    unfold verified_erasure_pipeline.
    rewrite -transform_compose_assoc.
    destruct_compose.
    cbn [transform pcuic_expand_lets_transform].
    rewrite (PCUICExpandLetsCorrectness.expand_lets_fo _ _ hv).
    cbn [fst snd].
    intros h.
    destruct_compose.
    destruct typing as [typing'], Heval.
    assert (eqtr : PCUICExpandLets.trans v = v).
    { clear -hv.
      move: v hv.
      eapply PCUICFirstorder.firstorder_value_inds.
      intros.
      rewrite PCUICExpandLetsCorrectness.trans_mkApps /=.
      f_equal. ELiftSubst.solve_all. }
    assert (PCUICFirstorder.firstorder_value (PCUICExpandLets.trans_global_env Σ.1, Σ.2) [] v).
    { eapply PCUICExpandLetsCorrectness.expand_lets_preserves_fo in hv; eauto. now rewrite eqtr in hv. }

    assert (Normalisation': PCUICSN.NormalizationIn (PCUICExpandLets.trans_global Σ)).
    { destruct h as [[] ?]. apply H0. cbn. apply X0. }
    set (Σ' := build_global_env_map _).
    set (p := transform erase_transform _ _).
    pose proof (@erase_tranform_firstorder guard _ h v i u (List.map PCUICExpandLets.trans args) Normalisation').
    forward H0.
    { cbn. rewrite -eqtr.
      eapply (PCUICClassification.subject_reduction_eval (Σ := Σ)) in X; tea.
      eapply PCUICExpandLetsCorrectness.expand_lets_sound in X.
      now rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in X. }
    forward H0. { cbn. now eapply (PCUICExpandLetsCorrectness.trans_axiom_free Σ). }
    forward H0.
    { cbn. clear -HΣ fo.
      move: fo. eapply PCUICExpandLetsCorrectness.trans_firstorder_ind. }
    forward H0. { cbn. rewrite -eqtr.
      unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ := Σ)); tea. exact extraction_checker_flags.
      apply HΣ. apply PCUICExpandLetsCorrectness.trans_wf, HΣ.
      2:{ eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X. }
      eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
      unshelve apply (PCUICClosedTyp.subject_closed typing'). }
    specialize (H0 _ eq_refl).
    rewrite /p.
    rewrite erase_transform_fo //.
    set (Σer := (transform erase_transform _ _).1).
    cbn [fst snd]. intros pre'.
    symmetry.
    destruct Heval as [Heval'].
    assert (firstorder_evalue Σer (compile_value_erase v [])).
    { apply H0. }
    erewrite transform_lambda_box_firstorder; tea.
    rewrite compile_evalue_strip //.
    destruct pre as [[wt] ?]. destruct wt.
    apply (compile_evalue_erase (PCUICExpandLets.trans_global Σ) Σer) => //.
    { cbn. now eapply (@PCUICExpandLetsCorrectness.trans_wf extraction_checker_flags Σ). }
    destruct H0. cbn -[transform erase_transform] in H0. apply H0.
  Qed.

  Import PCUICWfEnv.


  Lemma verified_erasure_pipeline_firstorder_evalue_block :
    firstorder_evalue_block Σ_v v_t.
  Proof.
    rewrite v_t_spec.
    unfold Σ_v.
    unfold verified_erasure_pipeline.
    repeat rewrite -transform_compose_assoc.
    destruct_compose.
    generalize fo_v. intros hv.
    cbn [transform pcuic_expand_lets_transform].
    intros pre1. destruct_compose. intros pre2.
    destruct (lambdabox_pres_fo econf) as [fn [tr hfn]].
    destruct tr. destruct typing as [typing']. pose proof (Heval' := Heval). sq. rewrite transform_fo.
    { intro. eapply preserves_fo. }
    assert (eqtr : PCUICExpandLets.trans v = v).
    { clear -hv.
      move: v hv.
      eapply PCUICFirstorder.firstorder_value_inds.
      intros.
      rewrite PCUICExpandLetsCorrectness.trans_mkApps /=.
      f_equal. ELiftSubst.solve_all. }
    assert (PCUICFirstorder.firstorder_value (PCUICExpandLets.trans_global_env Σ.1, Σ.2) [] v).
    { eapply PCUICExpandLetsCorrectness.expand_lets_preserves_fo in hv; eauto. now rewrite eqtr in hv. }
    assert (Normalisation': PCUICSN.NormalizationIn (PCUICExpandLets.trans_global Σ)).
    { destruct pre1 as [[] ?]. apply a. cbn. apply w. }
    set (Σ' := build_global_env_map (PCUICExpandLets.trans_global_env Σ.1)).
    set (p := transform erase_transform _ _).
    pose proof (@erase_tranform_firstorder guard _ pre1 v i u (List.map PCUICExpandLets.trans args) Normalisation').
    forward H0.
    { cbn.
      eapply (PCUICClassification.subject_reduction_eval (Σ := Σ)) in Heval'; tea.
      eapply PCUICExpandLetsCorrectness.expand_lets_sound in Heval'.
      now rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in Heval'. }
    forward H0. { now eapply PCUICExpandLetsCorrectness.trans_axiom_free. }
    forward H0.
    { cbn. clear -HΣ fo.
      move: fo.
      rewrite /PCUICFirstorder.firstorder_ind /= PCUICExpandLetsCorrectness.trans_lookup /=.
      destruct PCUICAst.PCUICEnvironment.lookup_env => //. destruct g => //=.
      eapply PCUICExpandLetsCorrectness.trans_firstorder_mutind. eapply PCUICExpandLetsCorrectness.trans_firstorder_env. }
    forward H0. { cbn. rewrite -eqtr.
      unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ := Σ)); tea. exact extraction_checker_flags.
      apply HΣ. apply PCUICExpandLetsCorrectness.trans_wf, HΣ.
      2:{ rewrite eqtr. eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in Heval'. }
      eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
      unshelve apply (PCUICClosedTyp.subject_closed typing'). now rewrite eqtr. }
    specialize (H0 _ eq_refl).
    rewrite /p.
    rewrite erase_transform_fo //. { cbn. rewrite eqtr. exact H. }
    set (Σer := (transform erase_transform _ _).1).
    assert (firstorder_evalue Σer (compile_value_erase v [])).
    { apply H0. }
    simpl. unfold fo_evalue_map. rewrite eqtr. exact H1.
  Qed.

  Lemma verified_erasure_pipeline_theorem :
    ∥ eval (wfl := extraction_wcbv_flags) Σ_t t_t v_t ∥.
  Proof.
    hnf.
    pose proof (preservation (verified_erasure_pipeline econf) (Σ, t)) as Hcorr.
    unshelve eapply Hcorr in Heval as Hev. eapply precond; eauto.
    destruct Hev as [v' [[H1] H2]].
    move: H2.
    rewrite v_t_spec.
    set (pre := precond2 _ _ _ _ _ _ _ _ _ _ _) in *. clearbody pre.
    subst v_t Σ_t t_t.
    revert H1.
    unfold verified_erasure_pipeline.
    intros.
    revert H1 H2. clear Hcorr.
    intros ev obs.
    cbn [obseq compose] in obs.
    unfold run, time in obs.
    decompose [ex and prod] obs. clear obs.
    subst.
    cbn [obseq compose erase_transform] in *.
    cbn [obseq compose pcuic_expand_lets_transform] in *.
    subst.
    move: ev b.
    repeat destruct_compose.
    intros.
    move: b.
    cbn [transform rebuild_wf_env_transform] in *.
    cbn [transform constructors_as_blocks_transformation] in *.
    cbn [transform inline_projections_optimization] in *.
    cbn [transform remove_match_on_box_trans] in *.
    cbn [transform remove_params_optimization] in *.
    cbn [transform guarded_to_unguarded_fix] in *.
    cbn [transform erase_transform] in *.
    cbn [transform compose pcuic_expand_lets_transform] in *.
    unfold run, time.
    cbn [obseq compose constructors_as_blocks_transformation] in *.
    cbn [obseq run compose rebuild_wf_env_transform] in *.
    cbn [obseq compose inline_projections_optimization] in *.
    cbn [obseq compose remove_match_on_box_trans] in *.
    cbn [obseq compose remove_params_optimization] in *.
    cbn [obseq compose guarded_to_unguarded_fix] in *.
    cbn [obseq compose erase_transform] in *.
    cbn [obseq compose pcuic_expand_lets_transform] in *.
    cbn [transform compose pcuic_expand_lets_transform] in *.
    cbn [transform erase_transform] in *.
    destruct Heval.
    pose proof typing as [typing']. pose proof typing as [typing''].
    eapply PCUICClassification.subject_reduction_eval in typing'; tea.
    eapply PCUICExpandLetsCorrectness.pcuic_expand_lets in typing'.
    rewrite PCUICExpandLetsCorrectness.trans_mkApps /= in typing'.
    destruct H1.
    (* pose proof (abstract_make_wf_env_ext) *)
    unfold PCUICExpandLets.expand_lets_program.
    set (em := build_global_env_map _).
    unfold erase_program.
    set (f := map_squash _ _). cbn in f.
    destruct H. destruct s as [[]].
    set (wfe := build_wf_env_from_env em (map_squash (PCUICTyping.wf_ext_wf (em, Σ.2)) (map_squash fst (conj (sq (w0, s)) a).p1))).
    destruct Heval.
    eapply (ErasureFunctionProperties.firstorder_erases_deterministic optimized_abstract_env_impl wfe Σ.2) in b0. 3:tea.
    2:{ cbn. reflexivity. }
    2:{ eapply PCUICExpandLetsCorrectness.trans_wcbveval. eapply PCUICWcbvEval.eval_closed; tea. apply HΣ.
        clear -typing'' HΣ. now eapply PCUICClosedTyp.subject_closed in typing''.
        eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X0. }
    (* 2:{ clear -fo. cbn. now eapply (PCUICExpandLetsCorrectness.trans_firstorder_ind Σ). }
        eapply PCUICWcbvEval.value_final. now eapply PCUICWcbvEval.eval_to_value in X. } *)
    2:{ clear -fo. revert fo. rewrite /PCUICFirstorder.firstorder_ind /=.
        rewrite PCUICExpandLetsCorrectness.trans_lookup.
        destruct PCUICAst.PCUICEnvironment.lookup_env => //.
        destruct g => //=.
        eapply PCUICExpandLetsCorrectness.trans_firstorder_mutind. eapply PCUICExpandLetsCorrectness.trans_firstorder_env. }
    2:{ apply HΣ. }
    2:{ apply PCUICExpandLetsCorrectness.trans_wf, HΣ. }
    rewrite b0. intros obs. constructor.
    match goal with [ H1 : eval _ _ ?v1 |- eval _ _ ?v2 ] => enough (v2 = v1) as -> by exact ev end.
    eapply obseq_lambdabox; revgoals.
    unfold erase_pcuic_program. cbn [fst snd]. exact obs.
    Unshelve. all:eauto.
    2:{ eapply PCUICExpandLetsCorrectness.trans_wf, HΣ. }
    clear obs b0 ev e w.
    eapply extends_erase_pcuic_program. cbn.
    unshelve eapply (PCUICExpandLetsCorrectness.trans_wcbveval (cf := extraction_checker_flags) (Σ := (Σ.1, Σ.2))).
    { now eapply PCUICExpandLetsCorrectness.trans_wf. }
    { clear -HΣ typing''. now eapply PCUICClosedTyp.subject_closed in typing''. }
    cbn. 2:cbn. exact X0.
    now eapply (PCUICExpandLetsCorrectness.trans_axiom_free Σ).
    pose proof (PCUICExpandLetsCorrectness.expand_lets_sound typing'').
    rewrite PCUICExpandLetsCorrectness.trans_mkApps in X1. eapply X1.
    cbn. eapply (PCUICExpandLetsCorrectness.trans_firstorder_ind Σ); eauto.
  Qed.

End pipeline_theorem.

(** Generalisations of [v_t_spec], [verified_erasure_pipeline_firstorder_evalue_block] and
    [verified_erasure_pipeline_lookup_env_in] to an arbitrary precondition proof [pr]. *)

Section pipeline_cond_gen.

  Variable Σ : global_env_ext_map.
  Variable t : PCUICAst.term.
  Variable T : PCUICAst.term.

  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.

  Variable typing : ∥PCUICTyping.typing Σ [] t T∥.

  Variable Normalisation : (forall Σ, wf_ext Σ -> PCUICSN.NormalizationIn Σ).
  Variable econf : erasure_configuration.

  Lemma verified_erasure_pipeline_lookup_env_in_gen pr kn decl (efl := ERemoveParams.switch_no_params all_env_flags)
    {has_rel : has_tRel} {has_box : has_tBox} :
    EGlobalEnv.lookup_env (transform (verified_erasure_pipeline econf) (Σ, t) pr).1 kn = Some decl ->
   exists decl',
    PCUICAst.PCUICEnvironment.lookup_global (PCUICExpandLets.trans_global_decls
    (PCUICAst.PCUICEnvironment.declarations Σ.1)) kn = Some decl'
    /\  erase_decl_equal (fun decl => ERemoveParams.strip_inductive_decl (erase_mutual_inductive_body decl))
           decl decl'.
  Proof.
    assert (pr = precond _ _ _ HΣ expΣ expt typing Normalisation econf) as -> by apply proof_irrelevance.
    intros hl. eapply verified_erasure_pipeline_lookup_env_in; eassumption.
  Qed.

End pipeline_cond_gen.

Section pipeline_theorem_gen.

  Variable Σ : global_env_ext_map.
  Variable HΣ : PCUICTyping.wf_ext Σ.
  Variable expΣ : PCUICEtaExpand.expanded_global_env Σ.1.

  Variable t : PCUICAst.term.
  Variable expt : PCUICEtaExpand.expanded Σ.1 [] t.
  Variable axfree : axiom_free Σ.
  Variable v : PCUICAst.term.

  Variable i : Kernames.inductive.
  Variable u : Universes.Instance.t.
  Variable args : list PCUICAst.term.

  Variable Normalisation :  (forall Σ, wf_ext Σ -> PCUICSN.NormalizationIn Σ).

  Variable typing : ∥PCUICTyping.typing Σ [] t (PCUICAst.mkApps (PCUICAst.tInd i u) args)∥.

  Variable fo : @PCUICFirstorder.firstorder_ind Σ (PCUICFirstorder.firstorder_env Σ) i.

  Variable Heval : ∥PCUICWcbvEval.eval Σ t v∥.

  Variable econf : erasure_configuration.

  Lemma v_t_spec_gen pr :
    compile_value_box (PCUICExpandLets.trans_global_env Σ) v [] =
    (transform (verified_erasure_pipeline econf) (Σ, v) pr).2.
  Proof.
    assert (pr = precond2 _ _ _ HΣ expΣ expt typing Normalisation econf _ Heval) as -> by apply proof_irrelevance.
    eapply v_t_spec; eauto.
  Qed.

  Lemma verified_erasure_pipeline_firstorder_evalue_block_gen pr :
    firstorder_evalue_block (transform (verified_erasure_pipeline econf) (Σ, v) pr).1
      (compile_value_box (PCUICExpandLets.trans_global_env Σ) v []).
  Proof.
    assert (pr = precond2 _ _ _ HΣ expΣ expt typing Normalisation econf _ Heval) as -> by apply proof_irrelevance.
    eapply verified_erasure_pipeline_firstorder_evalue_block; eauto.
  Qed.

End pipeline_theorem_gen.


End GenericPipeline.

About precond.
About precond2.
About v_t_spec.
About v_t_spec_gen.
About verified_erasure_pipeline_firstorder_evalue_block_gen.
About verified_erasure_pipeline_lookup_env_in_gen.
About pcuic_function_value.
About transform_erasure_pipeline_function'.

Print Assumptions precond.
Print Assumptions precond2.
Print Assumptions verified_erasure_pipeline_theorem.
Print Assumptions verified_erasure_pipeline_lookup_env_in.
Print Assumptions verified_erasure_pipeline_extends.
Print Assumptions verified_erasure_pipeline_firstorder_evalue_block.
Print Assumptions v_t_spec.
Print Assumptions erasure_pipeline_extends_app.
Print Assumptions transform_erasure_pipeline_function'.
Print Assumptions v_t_spec_gen.
Print Assumptions verified_erasure_pipeline_firstorder_evalue_block_gen.
Print Assumptions verified_erasure_pipeline_lookup_env_in_gen.

