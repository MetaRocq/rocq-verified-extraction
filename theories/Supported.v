From MetaRocq.Utils Require Import utils.
From MetaRocq.Erasure Require Import EAst ELiftSubst EGlobalEnv EWellformed EPrimitive EInduction EWcbvEvalNamed.
From Equations Require Import Equations.

(** * The fragment of named λ-box supported by the Malfunction backend

  [compile] (Compile.v) has no correct translation of [tLazy], [tForce] and of
  primitive strings and arrays.  The extraction flags [extraction_env_flags_mlf]
  rule them out, but [EWcbvEvalNamed.eval] has unconditional rules for them.
  [supported] / [supported_value] / [supported_env] capture the fragment
  without these constructs; [eval_supported] shows that evaluation stays inside
  it, so [CompileCorrect.compile_correct] never has to deal with them.  The
  remaining lemmas derive [supported] from well-formedness for flags that
  disable these constructs. *)

Definition supported_prim {A : Set} (p : prim_val A) : bool :=
  match projT1 p with
  | Primitive.primInt | Primitive.primFloat => true
  | _ => false
  end.

Fixpoint supported (t : term) : bool :=
  match t with
  | tEvar _ args => forallb supported args
  | tLambda _ b => supported b
  | tLetIn _ b b' => supported b && supported b'
  | tApp u v => supported u && supported v
  | tConstruct _ _ args => forallb supported args
  | tCase _ c brs => supported c && forallb (fun br => supported br.2) brs
  | tProj _ c => supported c
  | tFix mfix _ => forallb (fun d => supported d.(dbody)) mfix
  | tCoFix mfix _ => forallb (fun d => supported d.(dbody)) mfix
  | tPrim p => supported_prim p
  | tLazy _ => false
  | tForce _ => false
  | _ => true
  end.

Fixpoint supported_value (v : value) : bool :=
  match v with
  | vClos _ b env => supported b && forallb (fun x => supported_value x.2) env
  | vConstruct _ _ args => forallb supported_value args
  | vRecClos mfix _ env => forallb (fun d => supported d.2) mfix && forallb (fun x => supported_value x.2) env
  | vPrim p => supported_prim p
  | vLazy _ _ => false
  end.

Definition supported_ctx (Γ : environment) : bool :=
  forallb (fun x => supported_value x.2) Γ.

Definition supported_env (Σ : global_declarations) : Prop :=
  forall c decl body, declared_constant Σ c decl -> cst_body decl = Some body -> supported body.

Lemma supported_ctx_lookup Γ na v :
  supported_ctx Γ -> EWcbvEvalNamed.lookup Γ na = Some v -> supported_value v.
Proof.
  unfold supported_ctx, EWcbvEvalNamed.lookup.
  induction Γ as [ | [na' v'] Γ IH]; cbn; [congruence|].
  intros H. rtoProp. destruct String.eqb.
  - now intros [= ->].
  - eauto.
Qed.

Lemma supported_ctx_add na v Γ :
  supported_value v -> supported_ctx Γ -> supported_ctx (add na v Γ).
Proof.
  intros H1 H2. unfold supported_ctx, add; cbn. now rewrite H1.
Qed.

Lemma supported_ctx_add_multiple nms vs Γ :
  supported_ctx Γ -> forallb supported_value vs -> supported_ctx (add_multiple nms vs Γ).
Proof.
  induction vs in nms |- *; destruct nms; cbn; auto.
  intros ? ?. rtoProp. unfold supported_ctx in *; cbn. rtoProp; eauto.
Qed.

Lemma supported_fix_env mfix Γ :
  forallb (fun d => supported d.2) mfix -> supported_ctx Γ ->
  forallb supported_value (fix_env mfix Γ).
Proof.
  intros H1 H2. unfold fix_env. induction #|mfix|; cbn; auto.
Qed.

Lemma supported_map2_fix nms (mfix : mfixpoint term) :
  forallb (fun d => supported d.(dbody)) mfix ->
  forallb (fun d : Kernames.ident * term => supported d.2) (MRList.map2 (fun n d => (n, dbody d)) nms mfix).
Proof.
  induction mfix in nms |- *; destruct nms; cbn; auto.
  intros; rtoProp; split; auto.
Qed.

Lemma eval_supported Σ Γ s v :
  supported_env Σ ->
  eval Σ Γ s v -> supported_ctx Γ -> supported s -> supported_value v.
Proof.
  intros HΣ Heval. induction Heval; intros HΓ Hs; cbn in *; rtoProp.
  - eapply supported_ctx_lookup; eauto.
  - specialize (IHHeval1 HΓ H). cbn in IHHeval1. rtoProp.
    eapply IHHeval3; auto. unfold supported_ctx, add; cbn. rtoProp; auto.
  - auto.
  - eapply IHHeval2; auto. unfold supported_ctx, add; cbn. rtoProp; auto.
  - specialize (IHHeval1 HΓ H). cbn in IHHeval1.
    eapply IHHeval2.
    + now eapply supported_ctx_add_multiple.
    + exact (nth_error_forallb e1 H0).
  - specialize (IHHeval1 HΓ H). cbn in IHHeval1. rtoProp.
    pose proof (nth_error_forallb e0 H1) as Hfn. cbn in Hfn.
    eapply IHHeval2; auto. unfold supported_ctx, add; cbn. rtoProp; split; auto.
    eapply supported_ctx_add_multiple; auto.
    now eapply supported_fix_env.
  - rtoProp; split; auto. now eapply supported_map2_fix.
  - eapply IHHeval; eauto.
  - clear -IHa HΓ Hs. induction a; cbn in *; rtoProp; auto.
    destruct IHa as [IH1 IH2]. split; eauto.
  - auto.
  - destruct ev; cbn in *; congruence.
  - congruence.
  - congruence.
Qed.

Lemma All2_over_supported {Σ Γ} {Q : term -> value -> Type} {args args'} (a : All2_Set (eval Σ Γ) args args') :
  All2_over a (fun s v _ => supported_ctx Γ -> supported s -> Q s v) ->
  supported_ctx Γ -> forallb supported args ->
  All2_over a (fun s v _ => Q s v).
Proof.
  intros IH HΓ Hs. induction a; cbn in *; [exact tt|].
  rtoProp. destruct IH as [IH1 IH2]. split; auto.
Qed.

Section wellformed.
  Context {efl : EEnvFlags}.
  Context (Hlazy : has_tLazy_Force = false) (Hstr : has_primstring = false) (Harr : has_primarray = false).

  Lemma wellformed_supported Σ k t : wellformed Σ k t -> supported t.
  Proof.
    induction t using EInduction.term_forall_list_ind in k |- *; intros Hwf;
      cbn -[lookup_constructor lookup_constructor_pars_args wf_brs lookup_constant lookup_projection] in *; rtoProp; eauto.
    - solve_all.
    - destruct cstr_as_blocks; rtoProp.
      + solve_all.
      + destruct args; cbn in *; [reflexivity|discriminate].
    - split; [eauto|]. solve_all.
    - unfold wf_fix_gen in *. rtoProp. solve_all.
    - unfold wf_fix_gen in *. rtoProp. solve_all.
    - destruct p as [? []]; cbn in *; rtoProp; auto; congruence.
    - rewrite Hlazy in H; discriminate.
    - rewrite Hlazy in H; discriminate.
  Qed.

  Lemma wf_glob_supported_env Σ : wf_glob Σ -> supported_env Σ.
  Proof.
    intros Hwf c decl body Hdecl Hbody.
    unfold declared_constant in Hdecl.
    eapply lookup_env_wellformed in Hdecl; eauto. cbn in Hdecl.
    rewrite Hbody in Hdecl. cbn in Hdecl.
    eapply wellformed_supported; eauto.
  Qed.
End wellformed.
