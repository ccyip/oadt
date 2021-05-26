From oadt Require Import prelude.
From oadt Require Import lang_oadt.properties.

(** * Progress *)
(** The progress metatheorem. *)

Module M (atom_sig : AtomSig).

Include properties.M atom_sig.
Import syntax_notations.
Import semantics_notations.
Import typing_notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.


(** ** Canonical forms *)
Ltac canonical_form_solver :=
  inversion 1; intros; subst; eauto;
  apply_type_inv;
  apply_kind_inv;
  simpl_whnf_equiv.

Lemma canonical_form_unit Σ Γ e :
  val e ->
  Σ; Γ ⊢ e : 𝟙 ->
  e = <{ () }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_abs Σ Γ e τ2 τ1 :
  val e ->
  Σ; Γ ⊢ e : Π:τ2, τ1 ->
  exists e' τ, e = <{ \:τ => e' }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_bool Σ Γ e :
  val e ->
  Σ; Γ ⊢ e : 𝔹 ->
  exists b, e = <{ b }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_obool Σ Γ e :
  val e ->
  Σ; Γ ⊢ e : ~𝔹 ->
  exists b, e = <{ [b] }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_prod Σ Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 * τ2 ->
  exists v1 v2, val v1 /\ val v2 /\ e = <{ (v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_sum Σ Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 + τ2 ->
  exists b v τ, val v /\ e = <{ inj@b<τ> v }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_osum Σ Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 ~+ τ2 ->
  exists b v ω1 ω2, val v /\ otval ω1 /\ otval ω2 /\
               e = <{ [inj@b<ω1 ~+ ω2> v] }>.
Proof.
  canonical_form_solver;
    (* The cases when [e] is boxed injection. *)
    select (otval _) (fun H => sinvert H);
    repeat esplit; auto.
Qed.

(** Though it seems we should have a condition of [X] being an (public) ADT, this
condition is not needed since it is implied by the typing judgment. *)
Lemma canonical_form_fold Σ Γ e X :
  val e ->
  Σ; Γ ⊢ e : gvar X ->
  exists v X', val v /\ e = <{ fold<X'> v }>.
Proof.
  inversion 1; inversion 1; intros; subst; eauto;
  apply_type_inv;
  apply_kind_inv;
  simpl_whnf_equiv.
Qed.


(** ** Progress *)

(** Take a step through evaluation context. *)
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
Theorem progress_ Σ :
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
                  solve: step_ectx_solver
                  use: canonical_form_abs,
                       canonical_form_bool,
                       canonical_form_obool,
                       canonical_form_prod,
                       canonical_form_sum,
                       canonical_form_fold
          (* For oblivious type progress. *)
          | goal_contains otval;
            qauto q: on
                  ctrs: otval, step
                  solve: step_ectx_solver
                  use: canonical_form_bool,
                       canonical_form_sum
          | idtac ].

  (* [~case _ of _ | _] *)
  - right. intuition.
    (* Discriminee is value. *)
    + select (_; _ ⊢ _ : _) (fun H => apply canonical_form_osum in H); eauto.
      simp_hyps.
      select! (otval _) (fun H => use (oval_inhabited _ H)).
      hauto ctrs: step.
    (* Discriminee can take a step. *)
    + hauto solve: step_ectx_solver ctrs: step.

  (* [_ + _]. This case is impossible. *)
  - enough (<{ *@P }> ⊑ <{ *@O }>) by easy.
    scongruence use: join_ub_r.

  (* Kinding subsumption *)
  - select kind (fun κ => destruct κ); sintuition use: any_kind_otval.
Qed.

Theorem progress Σ τ e :
  Σ; ∅ ⊢ e : τ ->
  val e \/ exists e', Σ ⊨ e -->! e'.
Proof.
  hauto use: progress_.
Qed.

End M.
