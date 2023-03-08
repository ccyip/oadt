(** Properties of various value definitions. *)
From oadt.lang_oadt Require Import
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
  val v /\ otval ω /\ forall Σ Γ, Σ; Γ ⊢ v :{⊥} ω.
Proof.
  hauto use: ovalty_elim, oval_val.
Qed.

Lemma ovalty_intro v ω l Σ Γ :
  gctx_wf Σ ->
  oval v ->
  otval ω ->
  Σ; Γ ⊢ v :{l} ω ->
  ovalty v ω.
Proof.
  intros Hwf H. revert ω l.
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

Lemma ovalty_intro_alt v ω l Σ Γ :
  gctx_wf Σ ->
  val v ->
  otval ω ->
  Σ; Γ ⊢ v :{l} ω ->
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
  (* Case [`+]: we choose left injection as inhabitant. *)
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

Lemma wval_val Σ Γ τ v :
  Σ; Γ ⊢ v :{⊥} τ ->
  wval v ->
  val v.
Proof.
  remember ⊥.
  induction 1; subst; intros;
    try wval_inv; eauto using val, (bot_inv (A:=bool)).
Qed.

Lemma oval_safe Σ Γ v l τ :
  gctx_wf Σ ->
  Γ ⊢ v :{l} τ ->
  oval v ->
  l = ⊥.
Proof.
  intros Hwf Ht Hv.
  sinvert Hv; type_inv; eauto.
Qed.

Lemma val_wval v :
  val v ->
  wval v.
Proof.
  induction 1; eauto using wval.
Qed.

Lemma oval_wval v :
  oval v ->
  wval v.
Proof.
  eauto using oval_val, val_wval.
Qed.

Lemma woval_otval Σ Γ v l τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ v :{l} τ ->
  woval v ->
  exists ω, Σ; Γ ⊢ v :{l} ω /\ otval ω /\ Σ ⊢ ω ≡ τ.
Proof.
  intros Hwf.
  induction 1; intros Hv;
    try woval_inv; try oval_inv; simp_hyps;
    try solve [ repeat esplit; eauto;
                try lazymatch goal with
                    | |- _ ⊢ _ : _ =>
                        eauto using typing, otval_well_kinded with equiv_naive_solver
                    | |- _ ≡ _ => equiv_naive_solver
                    | |- otval _ => eauto using otval
                    end ].

  (* Oblivious pair *)
  select! (woval _ -> _) (fun H => feed specialize H; eauto using woval).
  simp_hyps.
  repeat esplit; eauto using typing, otval, otval_well_kinded.
  apply_pared_equiv_congr; eauto with lc.

  (* Promotion *)
  select! (woval _ -> _) (fun H => feed specialize H; eauto using woval).
  simp_hyps.
  repeat esplit; eauto using typing.
Qed.

Lemma woval_wval v :
  woval v ->
  wval v.
Proof.
  induction 1; eauto using wval, val_wval, oval_val.
Qed.

Lemma oval_woval v :
  oval v ->
  woval v.
Proof.
  eauto using woval.
Qed.

Lemma wval_otval v :
  wval v ->
  otval v ->
  False.
Proof.
  inversion 1; inversion 1; subst; oval_inv.
Qed.

Lemma val_otval v :
  val v ->
  otval v ->
  False.
Proof.
  eauto using wval_otval, val_wval.
Qed.

Section fix_gctx.

Context (Σ : gctx).
Set Default Proof Using "Type".

Lemma wval_step v e :
  v -->! e ->
  wval v ->
  False.
Proof.
  induction 1; intros; repeat ectx_inv;
    repeat wval_inv; repeat oval_inv; try step_inv; eauto using oval_wval, val_wval.
Qed.

Lemma otval_step ω e :
  ω -->! e ->
  otval ω ->
  False.
Proof.
  induction 1; intros; repeat ectx_inv; repeat otval_inv; try step_inv; eauto.
Qed.

Lemma val_step v e :
  v -->! e ->
  val v ->
  False.
Proof.
  eauto using wval_step, val_wval.
Qed.

Lemma wval_is_nf v :
  wval v ->
  nf (step Σ) v.
Proof.
  sfirstorder use: wval_step.
Qed.

Lemma otval_is_nf ω :
  otval ω ->
  nf (step Σ) ω.
Proof.
  sfirstorder use: otval_step.
Qed.

Lemma val_is_nf v :
  val v ->
  nf (step Σ) v.
Proof.
  sfirstorder use: val_step.
Qed.

End fix_gctx.
