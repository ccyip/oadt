From oadt.lang_oadt Require Import
     base syntax semantics typing indistinguishable infrastructure
     equivalence admissible inversion values preservation progress.
Import syntax.notations semantics.notations typing.notations
       equivalence.notations indistinguishable.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

(** * Properties of indistinguishability *)

Ltac indistinguishable_inv := safe_inv2 indistinguishable.

(** Indistinguishability is an equivalence. *)
#[global]
Instance indistinguishable_is_equiv : Equivalence indistinguishable.
Proof.
  split.
  - intros e. induction e; eauto using indistinguishable.
  - intros ??; induction 1; eauto using indistinguishable.
  - intros e1 e2 e3. intros H. revert e3.
    induction H; intros e3; inversion 1; subst; eauto using indistinguishable.
Qed.

Lemma indistinguishable_subst e e' s s' x :
  e ≈ e' ->
  s ≈ s' ->
  <{ {x↦s}e }> ≈ <{ {x↦s'}e' }>.
Proof.
  induction 1; intros; simpl in *;
    try case_decide; eauto using indistinguishable.
Qed.

Lemma indistinguishable_open e e' s s' :
  e ≈ e' ->
  s ≈ s' ->
  <{ e^s }> ≈ <{ e'^s' }>.
Proof.
  unfold open. intros H. generalize 0.
  induction H; intros; simpl in *;
    try case_decide; eauto using indistinguishable.
Qed.

Lemma indistinguishable_ovalty v v' ω :
  ovalty v ω ->
  ovalty v' ω ->
  v ≈ v'.
Proof.
  intros H. revert v'.
  induction H; intros v'; inversion 1; subst;
    eauto using indistinguishable.
Qed.

Lemma indistinguishable_ovalty_inv v v' ω ω' :
  v ≈ v' ->
  ovalty v ω ->
  ovalty v' ω' ->
  ω = ω'.
Proof.
  intros H. revert ω ω'.
  induction H; intros ??; inversion 1; subst; inversion 1; subst;
    qauto l: on inv: ovalty.
Qed.

Lemma indistinguishable_otval ω ω' :
  ω ≈ ω' ->
  otval ω ->
  otval ω'.
Proof.
  induction 1; intros; repeat otval_inv; qauto ctrs: otval.
Qed.

Lemma indistinguishable_otval_inv ω ω' :
  ω ≈ ω' ->
  otval ω ->
  otval ω' ->
  ω = ω'.
Proof.
  induction 1; intros; repeat otval_inv; qauto.
Qed.

Lemma indistinguishable_oval v v' :
  v ≈ v' ->
  oval v ->
  lc v' ->
  oval v'.
Proof.
  induction 1; intros; repeat oval_inv; repeat lc_inv; eauto using oval.
Qed.

Lemma indistinguishable_val_ v v' :
  v ≈ v' ->
  val v ->
  lc v' ->
  val v'.
Proof.
  induction 1; intros;
    repeat val_inv; repeat oval_inv; repeat lc_inv;
    eauto using val, oval, indistinguishable_oval.
Qed.

Lemma indistinguishable_val v v' Σ Γ τ :
  v ≈ v' ->
  val v ->
  Σ; Γ ⊢ v' : τ ->
  val v'.
Proof.
  qauto use: indistinguishable_val_, typing_lc.
Qed.

Section fix_gctx.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "Hwf".

(** [indistinguishable_obliv_val] and [indistinguishable_val_type] are two of
the most important lemmas. *)

Lemma indistinguishable_obliv_val Γ v v' τ :
  Γ ⊢ v : τ ->
  Γ ⊢ v' : τ ->
  val v ->
  val v' ->
  Γ ⊢ τ :: *@O ->
  v ≈ v'.
Proof.
  intros H. revert v'.
  induction H; intros;
    repeat val_inv;
    repeat oval_inv;
    try apply_regularity;
    try apply_canonical_form;
    type_inv;
    kind_inv;
    try simpl_whnf_equiv;
    simplify_eq;
    try solve [ easy
              | econstructor; auto_eapply; eauto;
                econstructor; eauto with equiv_naive_solver ].

  (* Boxed injection *)
  - ovalty_inv.
    apply_canonical_form.
    type_inv.
    kind_inv.
    select (_ ≡ _) (fun H => eapply otval_uniq in H;
                           eauto using otval; rewrite H).
    econstructor.

  (* Equivalence case *)
  - auto_eapply; eauto.
    econstructor; eauto with equiv_naive_solver.
    eapply pared_equiv_obliv_preservation; eauto; equiv_naive_solver.
Qed.

Lemma indistinguishable_val_obliv_type_equiv Γ v v' τ τ' :
  Γ ⊢ v : τ ->
  Γ ⊢ v' : τ' ->
  Γ ⊢ τ :: *@O ->
  val v ->
  v ≈ v' ->
  τ ≡ τ'.
Proof.
  intros H. revert v' τ'.
  induction H; intros;
    try indistinguishable_inv;
    repeat val_inv;
    repeat oval_inv;
    try apply_regularity;
    type_inv;
    kind_inv;
    simplify_eq;
    try easy.

  (* Oblivious product *)
  - etrans; [ | symmetry; eauto ].
    apply_pared_equiv_congr; eauto using kinding_lc, typing_type_lc;
      auto_eapply; eauto using kinding, oval_val.

  (* Equivalence case *)
  - etrans; try auto_eapply; eauto with equiv_naive_solver.
    eapply pared_equiv_obliv_preservation; eauto; equiv_naive_solver.
Qed.

(* This lemma can be strengthened so that we drop the typing assumption for
[v']. In order for that, we have to prove [v'] can be typed which should be
provable. But this version is good enough for the main theorem. *)
Lemma indistinguishable_val_type Γ v v' τ τ' :
  Γ ⊢ v : τ ->
  Γ ⊢ v' : τ' ->
  Γ ⊢ τ :: *@O ->
  val v ->
  v ≈ v' ->
  Γ ⊢ v' : τ.
Proof.
  intros.
  eapply TConv; eauto.
  symmetry.
  eapply indistinguishable_val_obliv_type_equiv; eauto.
Qed.

Ltac val_step_absurd :=
  match goal with
  | H : _ -->! _ |- _ =>
    exfalso; eapply otval_step;
    [ apply H
    | solve [ eauto
            | eapply indistinguishable_otval;
              [ solve [ eassumption | symmetry; eassumption ]
              | eauto using otval ] ] ]
  | H : _ -->! _ |- _ =>
    exfalso; eapply val_step;
    [ apply H
    | solve [ eauto using val
            | eapply indistinguishable_val;
              [ solve [ eassumption | symmetry; eassumption ]
              | eauto using val
              | eauto ] ] ]
  end.

(** * Obliviousness theorem *)

Lemma indistinguishable_step e1 e1' e2 τ1 τ2 :
  e1 -->! e1' ->
  e1 ≈ e2 ->
  ∅ ⊢ e1 : τ1 ->
  ∅ ⊢ e2 : τ2 ->
  exists e2', e2 -->! e2'.
Proof.
  qauto use: progress solve: val_step_absurd.
Qed.

Lemma indistinguishable_deterministic e1 e1' e2 e2' :
  e1 -->! e1' ->
  e2 -->! e2' ->
  e1 ≈ e2 ->
  ((exists τ1 τ2, ∅ ⊢ e1 : τ1 /\ ∅ ⊢ e2 : τ2) \/
   (exists κ1 κ2, ∅ ⊢ e1 :: κ1 /\ ∅ ⊢ e2 :: κ2)) ->
  e1' ≈ e2'.
Proof.
  intros H. revert e2 e2'.
  induction H; intros;
    repeat ectx_inv; simplify_eq;
    repeat
      (repeat indistinguishable_inv;
       try (select (_ \/ _) (fun H => destruct H); simp_hyps);
       type_inv; kind_inv; simplify_eq;
       try step_inv;
       try solve
           (* Discharge the impossible cases *)
           [ val_step_absurd
           (* Solve the trivial cases *)
           | eauto using indistinguishable, indistinguishable_open
           (* Solve the inductive cases. *)
           | econstructor; eauto; auto_eapply; eauto 10 using kinding ]);
    (* Solve other less trivial cases *)
    try qauto rew: off use: indistinguishable_open solve: reflexivity.

  (* Step from oblivious injection to boxed injection *)
  - match goal with
    | |- <{ [inj@_< ?ω1 > _] }> ≈ <{ [inj@_< ?ω2 > _] }> =>
      replace ω2 with ω1
        by (eauto using indistinguishable, indistinguishable_otval_inv)
    end.
    eauto using indistinguishable.

  (* Step from oblivious case to mux *)
  - repeat ovalty_inv;
    econstructor; eauto using indistinguishable;
      case_splitting;
      eauto using indistinguishable_open, indistinguishable_ovalty.

  (* Step from mux *)
  - case_splitting;
      eauto using indistinguishable_obliv_val, indistinguishable_val_type.
Qed.

(** The one-step obliviousness theorem, which is essentially a noninterference
theorem. Two indistinguishable well-typed expressions always step to
indistinguishable new expressions, or they both can not take any more step. It
is important that if one of them takes step, another one also takes step.
Otherwise the adversaries can distinguish them by this mismatched behavior. *)
Corollary obliviousness_step e1 e1' e2 τ1 τ2 :
  e1 -->! e1' ->
  e1 ≈ e2 ->
  ∅ ⊢ e1 : τ1 ->
  ∅ ⊢ e2 : τ2 ->
  (exists e2', e2 -->! e2') /\
  (forall e2', e2 -->! e2' -> e1' ≈ e2').
Proof.
  hauto use: indistinguishable_step, indistinguishable_deterministic.
Qed.

End fix_gctx.
