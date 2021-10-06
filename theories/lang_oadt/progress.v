From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.values.
From oadt Require Import lang_oadt.admissible.
From oadt Require Import lang_oadt.inversion.
From oadt Require Import lang_oadt.equivalence.

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

Section progress.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

Set Default Proof Using "Hwf".

(** * Canonical forms *)
Ltac canonical_form_solver :=
  inversion 1; intros; subst; eauto;
  apply_type_inv;
  apply_kind_inv;
  simpl_whnf_equiv.

Lemma canonical_form_unit Γ e :
  val e ->
  Σ; Γ ⊢ e : 𝟙 ->
  e = <{ () }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_abs Γ e τ2 τ1 :
  val e ->
  Σ; Γ ⊢ e : Π:τ2, τ1 ->
  exists e' τ, e = <{ \:τ => e' }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_bool Γ e :
  val e ->
  Σ; Γ ⊢ e : 𝔹 ->
  exists b, e = <{ b }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_obool Γ e :
  val e ->
  Σ; Γ ⊢ e : ~𝔹 ->
  exists b, e = <{ [b] }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_prod Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 * τ2 ->
  exists v1 v2, val v1 /\ val v2 /\ e = <{ (v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_sum Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 + τ2 ->
  exists b v τ, val v /\ e = <{ inj@b<τ> v }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_osum Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 ~+ τ2 ->
  exists b v ω1 ω2, oval v /\ otval ω1 /\ otval ω2 /\
               e = <{ [inj@b<ω1 ~+ ω2> v] }>.
Proof.
  canonical_form_solver.

  (* The cases when [e] is boxed injection. *)
  select (otval _) (fun H => sinvert H);
  repeat esplit; auto.
Qed.

(** Though it seems we should have a condition of [X] being an (public) ADT, this
condition is not needed since it is implied by the typing judgment. *)
Lemma canonical_form_fold Γ e X :
  val e ->
  Σ; Γ ⊢ e : gvar X ->
  exists v X', val v /\ e = <{ fold<X'> v }>.
Proof.
  inversion 1; inversion 1; intros; subst; eauto;
  apply_type_inv;
  apply_kind_inv;
  simplify_eq;
  simpl_whnf_equiv.
Qed.


(** * Progress *)

(** Dealing with evaluation context. *)
Ltac step_ectx_solver :=
  match goal with
  | H : _ ⊨ _ -->! _ |- exists _, _ ⊨ _ -->! _ =>
    eexists;
    eapply SCtx_intro;
    [ solve [apply H]
    | higher_order_reflexivity
    | higher_order_reflexivity
    | solve [constructor; eauto] ]
  end.

(** The combined progress theorems for expressions and types. *)
Theorem progress_ :
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      Γ = ∅ ->
      val e \/ exists e', Σ ⊨ e -->! e') /\
  (forall Γ τ κ,
     Σ; Γ ⊢ τ :: κ ->
     Γ = ∅ ->
     κ = <{ *@O }> ->
     otval τ \/ exists τ', Σ ⊨ τ -->! τ').
Proof.
  apply typing_kinding_mutind; intros; subst;
    (* If a type is not used in the conclusion, the mutual inductive hypothesis
    for it is useless. Remove this hypothesis to avoid slowdown the
    automation. *)
    try match goal with
        | H : context [otval ?τ \/ _] |- val ?e \/ _ =>
          assert_fails contains e τ; clear H
        end;
    (* Try solve the boring cases, unless they are the trickier ones. *)
    first [ goal_is (val <{ ~case _ of _ | _ }> \/ _)
          | goal_is (otval <{ _ + _ }> \/ _)
          | match goal with
            | |- otval ?τ \/ _ => is_var τ
            end
          (* Take care of the simple cases. *)
          | goal_is (val <{ [inj@_<_> _] }> \/ _); sfirstorder use: oval_elim
          | qauto q: on rew: off
                  simp: simpl_map
                  ctrs: val, otval, step, ectx
          (* Take care of the more complex cases involving evaluation context. *)
          (* For expression progress. *)
          | goal_contains val;
            qauto q: on
                  ctrs: val, step
                  use: canonical_form_abs,
                       canonical_form_bool,
                       canonical_form_obool,
                       canonical_form_prod,
                       canonical_form_sum,
                       canonical_form_fold
                  solve: step_ectx_solver
          (* For oblivious type progress. *)
          | goal_contains otval;
            qauto q: on
                  ctrs: otval, step
                  use: canonical_form_bool,
                       canonical_form_sum
                  solve: step_ectx_solver
          | idtac ].

  (* Injection *)
  - right. intuition; try qauto solve: step_ectx_solver.
    (* Step to boxed injection *)
    eexists. econstructor; eauto.
    qauto l: on ctrs: otval inv: otval use: ovalty_elim, ovalty_intro_alt.

  (* [~case _ of _ | _] *)
  - right. intuition.
    (* Discriminee is value. *)
    + select (_; _ ⊢ _ : _) (fun H => apply canonical_form_osum in H); eauto.
      simp_hyps.
      select! (otval _) (fun H => use (ovalty_inhabited _ H)).
      hauto ctrs: step.
    (* Discriminee can take a step. *)
    + hauto ctrs: step solve: step_ectx_solver.

  (* [[inj@_<_> _]] *)
  - sfirstorder use: ovalty_elim_alt.

  (* [_ + _]. This case is impossible. *)
  - enough (<{ *@P }> ⊑ <{ *@O }>) by easy.
    scongruence use: join_ub_r.

  (* Kinding subsumption *)
  - select kind (fun κ => destruct κ); sintuition use: any_kind_otval.
Qed.

Theorem progress τ e :
  Σ; ∅ ⊢ e : τ ->
  val e \/ exists e', Σ ⊨ e -->! e'.
Proof.
  hauto use: progress_.
Qed.

Theorem kinding_progress τ :
  Σ; ∅ ⊢ τ :: *@O ->
  otval τ \/ exists τ', Σ ⊨ τ -->! τ'.
Proof.
  hauto use: progress_.
Qed.

End progress.
