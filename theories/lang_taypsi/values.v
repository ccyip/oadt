(** Properties of various value definitions. *)
From taypsi.lang_taypsi Require Import
     base syntax semantics typing infrastructure
     equivalence inversion.
Import syntax.notations semantics.notations typing.notations equivalence.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

Lemma oval_val v :
  oval v ->
  val v.
Proof.
  eauto using val.
Qed.

Lemma otval_uniq Σ ω1 ω2 :
  otval ω1 ->
  otval ω2 ->
  Σ ⊢ ω1 ≡ ω2 ->
  ω1 = ω2.
Proof.
  intros H. revert ω2.
  induction H; intros; simpl_whnf_equiv;
    qauto l:on rew:off inv: otval.
Qed.

Lemma ovalty_elim_alt v ω:
  ovalty v ω ->
  val v /\ otval ω /\ forall Σ Γ, Σ; Γ ⊢ v : ω.
Proof.
  hauto use: ovalty_elim, oval_val.
Qed.

Lemma ovalty_intro v ω Σ Γ :
  gctx_wf Σ ->
  oval v ->
  otval ω ->
  Σ; Γ ⊢ v : ω ->
  ovalty v ω.
Proof.
  intros Hwf H. revert ω.
  induction H; inversion 1; intros; subst;
    type_inv;
    simpl_whnf_equiv;
    try hauto lq: on rew: off
              ctrs: ovalty, typing
              use: otval_well_kinded
              solve: equiv_naive_solver.

  (* Case [inj@_<_> _] *)
  select! (_ ≡ _) (fun H => apply otval_uniq in H); subst; eauto using ovalty;
    qauto l: on use: ovalty_elim inv: otval.
Qed.

Lemma ovalty_intro_alt v ω Σ Γ :
  gctx_wf Σ ->
  val v ->
  otval ω ->
  Σ; Γ ⊢ v : ω ->
  ovalty v ω.
Proof.
  destruct 2; eauto using ovalty_intro; inversion 1; intros; subst;
    type_inv;
    simpl_whnf_equiv.
Qed.

(** We can always find an inhabitant for any oblivious type value. *)
Lemma ovalty_inhabited ω :
  otval ω ->
  exists v, ovalty v ω.
Proof.
  induction 1; try qauto ctrs: ovalty.
  (* Case [~+]: we choose left injection as inhabitant. *)
  sfirstorder use: (OTOSum true).
Qed.

Lemma any_kind_otval Σ Γ τ :
  Σ; Γ ⊢ τ :: *@A ->
  otval τ.
Proof.
  remember <{ *@A }>.
  induction 1; subst; try hauto ctrs: otval.
  - srewrite join_bot_iff. easy.
  - srewrite join_bot_iff. easy.
  - eauto using bot_inv.
Qed.

Lemma val_otval v :
  val v ->
  otval v ->
  False.
Proof.
  induction 2; intros; try val_inv; try oval_inv; eauto.
Qed.

Section fix_gctx.

Context (Σ : gctx).
Set Default Proof Using "Type".

Lemma val_step v e :
  v -->! e ->
  val v ->
  False.
Proof.
  induction 1; intros; repeat ectx_inv;
    repeat val_inv; repeat oval_inv; try step_inv; eauto using oval_val.
Qed.

Lemma otval_step ω e :
  ω -->! e ->
  otval ω ->
  False.
Proof.
  induction 1; intros; repeat ectx_inv; repeat otval_inv; try step_inv; eauto.
Qed.

Lemma val_is_nf v :
  val v ->
  nf (step Σ) v.
Proof.
  sfirstorder use: val_step.
Qed.

Lemma otval_is_nf ω :
  otval ω ->
  nf (step Σ) ω.
Proof.
  sfirstorder use: otval_step.
Qed.

End fix_gctx.
