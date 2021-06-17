From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.properties.
From oadt Require Import lang_oadt.admissible.
From oadt Require Import lang_oadt.inversion.
From oadt Require Import lang_oadt.equivalence.
From oadt Require Import lang_oadt.progress.
From oadt Require Import lang_oadt.preservation.

(** * Obliviousness *)
(** The obliviousness metatheorem. Essentially a noninterference property. *)

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

Lemma pared_obliv_preservation_inv Σ Γ τ τ' κ :
  gctx_wf Σ ->
  Σ ⊢ τ ==>! τ' ->
  Σ; Γ ⊢ τ :: κ ->
  Σ; Γ ⊢ τ' :: *@O ->
  Σ; Γ ⊢ τ :: *@O.
Proof.
  intros Hwf.
  induction 1; intros; try case_label;
    apply_kind_inv;
    simpl_cofin?;
    simplify_eq;
    try solve [ kinding_intro; eauto; set_shelve ];
    try easy.

  (* Product *)
  hauto ctrs: kinding solve: lattice_naive_solver.

  Unshelve.
  all : fast_set_solver!!.
Qed.

Lemma pared_equiv_obliv_preservation Σ Γ τ τ' κ :
  gctx_wf Σ ->
  Σ ⊢ τ ≡ τ' ->
  Σ; Γ ⊢ τ :: *@O ->
  Σ; Γ ⊢ τ' :: κ ->
  Σ; Γ ⊢ τ' :: *@O.
Proof.
  intros Hwf.
  induction 1; intros;
    eauto using pared_obliv_preservation_inv, pared_kinding_preservation.
Qed.

(** Indistinguishability is equivalence. *)
Instance indistinguishable_is_equiv : Equivalence indistinguishable.
Proof.
  split.
  - intros e. induction e; eauto using indistinguishable.
  - intros ??; induction 1; eauto using indistinguishable.
  - intros e1 e2 e3. intros H. revert e3.
    induction H; intros e3; inversion 1; subst; eauto using indistinguishable.
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
  induction 1; intros;
    qauto l: on inv: otval ctrs: otval.
Qed.

Lemma indistinguishable_otval_inv ω ω' :
  ω ≈ ω' ->
  otval ω ->
  otval ω' ->
  ω = ω'.
Proof.
  induction 1; intros;
    qauto l: on inv: otval.
Qed.

Lemma indistinguishable_val_ v v' :
  v ≈ v' ->
  val v ->
  lc v' ->
  val v'.
Proof.
  induction 1; intros; try qauto l: on ctrs: val inv: val, lc.
Qed.

Lemma indistinguishable_val v v' Σ Γ τ :
  v ≈ v' ->
  val v ->
  Σ; Γ ⊢ v' : τ ->
  val v'.
Proof.
  qauto use: indistinguishable_val_, typing_lc.
Qed.

Lemma indistinguishable_val_is_nf Σ v v' :
  val v ->
  v ≈ v' ->
  nf (@step Σ) v'.
Proof.
  intros H. revert v'.
  induction H; intros ?? [];
    select (_ ≈ _) (fun H => sinvert H);
    select (_ ⊨ _ -->! _) (fun H => sinvert H);
    try select (ectx _) (fun H => sinvert H);
    simplify_eq; eauto; sfirstorder.
Qed.

Lemma indistinguishable_otval_is_nf Σ ω ω' :
  otval ω ->
  ω ≈ ω' ->
  nf (@step Σ) ω'.
Proof.
  intros H. revert ω'.
  induction H; intros ?? [];
    select (_ ≈ _) (fun H => sinvert H);
    select (_ ⊨ _ -->! _) (fun H => sinvert H);
    try select (ectx _) (fun H => sinvert H);
    simplify_eq; eauto; sfirstorder.
Qed.

Lemma indistinguishable_val_step Σ v v' e :
  val v ->
  v ≈ v' ->
  Σ ⊨ v' -->! e ->
  False.
Proof.
  sfirstorder use: indistinguishable_val_is_nf.
Qed.

Lemma indistinguishable_otval_step Σ ω ω' e :
  otval ω ->
  ω ≈ ω' ->
  Σ ⊨ ω' -->! e ->
  False.
Proof.
  sfirstorder use: indistinguishable_otval_is_nf.
Qed.

(** The next few lemmas can be proved independently, but they can simply reduce
to the indistinguishable counterparts. *)
Lemma val_is_nf Σ v :
  val v ->
  nf (@step Σ) v.
Proof.
  qauto use: indistinguishable_val_is_nf solve: reflexivity.
Qed.

Lemma otval_is_nf Σ ω :
  otval ω ->
  nf (@step Σ) ω.
Proof.
  qauto use: indistinguishable_otval_is_nf solve: reflexivity.
Qed.

Lemma val_step Σ v e :
  Σ ⊨ v -->! e ->
  val v ->
  False.
Proof.
  sfirstorder use: val_is_nf.
Qed.

Lemma otval_step Σ ω e :
  Σ ⊨ ω -->! e ->
  otval ω ->
  False.
Proof.
  sfirstorder use: otval_is_nf.
Qed.


Ltac apply_canonical_form_ H τ :=
  lazymatch τ with
  | <{ 𝟙 }> => eapply canonical_form_unit in H
  | <{ ~𝔹 }> => eapply canonical_form_obool in H
  | <{ _ * _ }> => eapply canonical_form_prod in H
  | <{ _ ~+ _ }> => eapply canonical_form_osum in H
  end.

(* This tactic is destructive. *)
Ltac apply_canonical_form :=
  match goal with
  | H : val ?e, H' : _; _ ⊢ ?e : ?τ |- _ =>
    apply_canonical_form_ H τ; eauto; try simp_hyp H
  end; subst.

Lemma indistinguishable_obliv_val Σ Γ v v' τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ v : τ ->
  Σ; Γ ⊢ v' : τ ->
  val v ->
  val v' ->
  Σ; Γ ⊢ τ :: *@O ->
  v ≈ v'.
Proof.
  intros Hwf H. revert v'.
  induction H; intros;
    repeat
      match goal with
      | H : val ?e |- _ => head_constructor e; sinvert H
      end; simplify_eq;
      try apply_regularity;
      try apply_canonical_form;
      apply_type_inv;
      apply_kind_inv;
      try simpl_whnf_equiv;
      simplify_eq;
      try solve [ easy
                | econstructor; auto_apply; eauto;
                  econstructor; eauto; equiv_naive_solver ].

  (* Boxed injection *)
  - select (ovalty _ _) (fun H => sinvert H).
    apply_canonical_form.
    apply_type_inv.
    apply_kind_inv.
    select (_ ⊢ _ ≡ _) (fun H => eapply otval_uniq in H;
                               eauto using otval; rewrite H).
    econstructor.

  (* Equivalence case *)
  - auto_apply; eauto.
    econstructor; eauto; equiv_naive_solver.
    eapply pared_equiv_obliv_preservation; eauto; equiv_naive_solver.
Qed.

Lemma indistinguishable_val_obliv_type_equiv Σ Γ v v' τ τ' :
  gctx_wf Σ ->
  Σ; Γ ⊢ v : τ ->
  Σ; Γ ⊢ v' : τ' ->
  Σ; Γ ⊢ τ :: *@O ->
  val v ->
  v ≈ v' ->
  Σ ⊢ τ ≡ τ'.
Proof.
  intros Hwf H. revert v' τ'.
  induction H; intros;
    try match goal with
        | H : ?e ≈ _ |- _ => head_constructor e; sinvert H
        end; simplify_eq;
    repeat
      match goal with
      | H : val ?e |- _ => head_constructor e; sinvert H
      end; simplify_eq;
      try apply_regularity;
      apply_type_inv;
      apply_kind_inv;
      simplify_eq;
      try easy.

  (* Product *)
  - select (_ ⊢ _ ≡ _ * _) (fun H => rewrite H).
    apply_pared_equiv_congr; eauto using kinding_lc, typing_type_lc;
      auto_eapply; eauto using kinding.

  (* Equivalence case *)
  - etrans; try auto_eapply; eauto.
    equiv_naive_solver.
    eapply pared_equiv_obliv_preservation; eauto; equiv_naive_solver.
Qed.

(* This lemma can be strengthened so that we drop the typing assumption for
[v']. In order for that, we have to prove [v'] can be typed which should be
provable. But this version is good enough for the main theorem. *)
Lemma indistinguishable_val_type Σ Γ v v' τ τ' :
  gctx_wf Σ ->
  Σ; Γ ⊢ v : τ ->
  Σ; Γ ⊢ v' : τ' ->
  Σ; Γ ⊢ τ :: *@O ->
  val v ->
  v ≈ v' ->
  Σ; Γ ⊢ v' : τ.
Proof.
  intros.
  eapply TConv; eauto.
  symmetry.
  eapply indistinguishable_val_obliv_type_equiv; eauto.
Qed.

Ltac val_step_absurd :=
  match goal with
  | H : _ ⊨ _ -->! _ |- _ =>
    exfalso; eapply otval_step;
    [ apply H
    | solve [ eauto
            | eapply indistinguishable_otval;
              [ solve [ eassumption | symmetry; eassumption ]
              | eauto using otval ] ] ]
  | H : _ ⊨ _ -->! _ |- _ =>
    exfalso; eapply val_step;
    [ apply H
    | solve [ eauto
            | eapply indistinguishable_val;
              [ solve [ eassumption | symmetry; eassumption ]
              | eauto using val
              | eauto ] ] ]
  end.

Lemma indistinguishable_step Σ e1 e1' e2 τ τ' :
  gctx_wf Σ ->
  Σ ⊨ e1 -->! e2 ->
  e1 ≈ e1' ->
  Σ; ∅ ⊢ e1 : τ ->
  Σ; ∅ ⊢ e1' : τ' ->
  exists e2', Σ ⊨ e1' -->! e2'.
Proof.
  intros.
  qauto use: progress solve: val_step_absurd.
Qed.

Lemma indistinguishable_deterministic Σ e1 e1' e2 e2' :
  gctx_wf Σ ->
  Σ ⊨ e1 -->! e2 ->
  Σ ⊨ e1' -->! e2' ->
  e1 ≈ e1' ->
  ((exists τ τ', Σ; ∅ ⊢ e1 : τ /\ Σ; ∅ ⊢ e1' : τ') \/
   (exists κ κ', Σ; ∅ ⊢ e1 :: κ /\ Σ; ∅ ⊢ e1' :: κ')) ->
  e2 ≈ e2'.
Proof.
  intros Hwf H. revert e1' e2'.
  induction H; intros;
    try select (ectx _) (fun H => sinvert H); simplify_eq;
      repeat
        (match goal with
         | H : ?e ≈ _ |- _ => head_constructor e; sinvert H
         | H : _ ≈ ?e |- _ => head_constructor e; sinvert H
         end;
         try (select (_ \/ _) (fun H => destruct H as [ [?[?[??]]] | [?[?[??]]] ]));
         apply_type_inv; apply_kind_inv;
         try match goal with
             | H : _ ⊨ ?e -->! _ |- _ =>
               head_constructor e; sinvert H
             end;
         try select (ectx _) (fun H => sinvert H); simplify_eq;
         try select (oval _) (fun H => apply oval_val in H);
         try solve
             (* Discharge the impossible cases *)
             [ val_step_absurd
             (* Solve the trivial cases *)
             | eauto using indistinguishable_open
             (* Solve the inductive cases. *)
             | econstructor; eauto; auto_eapply; eauto 10 using kinding ]);
      (* Solve other less trivial cases *)
      try qauto rew: off use: indistinguishable_open solve: reflexivity.

  (* Step from oblivious case to mux *)
  - repeat
      match goal with
      | H : ovalty ?v _ |- _ => head_constructor v; sinvert H
      end.
    econstructor; eauto using indistinguishable;
      case_splitting;
      eauto using indistinguishable_open, indistinguishable_ovalty.

  (* Step from oblivious injection to boxed injection *)
  - match goal with
    | |- <{ [inj@_< ?ω1 > _] }> ≈ <{ [inj@_< ?ω2 > _] }> =>
      replace ω2 with ω1
        by (eauto using indistinguishable, indistinguishable_otval_inv)
    end.
    eauto using indistinguishable.

  (* Step from mux *)
  - case_splitting;
      eauto using indistinguishable_obliv_val, indistinguishable_val_type.

Qed.

(** The one-step obliviousness theorem, which is essentially a noninterference
theorem. Two indistinguishable well-typed expressions always step to
indistinguishable new expressions, or they both can not take any more step. It
is important that if one of them takes step, another one also takes step.
Otherwise the adversaries can distinguish them by this mismatched behavior. *)
Corollary obliviousness_step Σ e1 e1' e2 τ τ' :
  gctx_wf Σ ->
  Σ ⊨ e1 -->! e2 ->
  e1 ≈ e1' ->
  Σ; ∅ ⊢ e1 : τ ->
  Σ; ∅ ⊢ e1' : τ' ->
  (exists e2', Σ ⊨ e1' -->! e2') /\
  (forall e2', Σ ⊨ e1' -->! e2' -> e2 ≈ e2').
Proof.
  qauto use: indistinguishable_step, indistinguishable_deterministic.
Qed.
