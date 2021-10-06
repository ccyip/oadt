From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.values.
From oadt Require Import lang_oadt.admissible.
From oadt Require Import lang_oadt.inversion.
From oadt Require Import lang_oadt.equivalence.
From oadt Require Import lang_oadt.preservation.

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

Section progress.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "Hwf".

(** * Lemmas about obliviousness *)

Lemma pared_obliv_preservation_inv Γ τ τ' κ :
  Σ ⊢ τ ==>! τ' ->
  Σ; Γ ⊢ τ :: κ ->
  Σ; Γ ⊢ τ' :: *@O ->
  Σ; Γ ⊢ τ :: *@O.
Proof.
  induction 1; intros; try case_label;
    kind_inv;
    simpl_cofin?;
    simplify_eq;
    try solve [ kinding_intro; eauto; set_shelve ];
    try easy.

  (* Product *)
  hauto ctrs: kinding solve: lattice_naive_solver.

  Unshelve.
  all : fast_set_solver!!.
Qed.

Lemma pared_equiv_obliv_preservation Γ τ τ' κ :
  Σ ⊢ τ ≡ τ' ->
  Σ; Γ ⊢ τ :: *@O ->
  Σ; Γ ⊢ τ' :: κ ->
  Σ; Γ ⊢ τ' :: *@O.
Proof.
  induction 1; intros;
    eauto using pared_obliv_preservation_inv, pared_kinding_preservation.
Qed.

Lemma wval_woval Γ v l τ :
  Σ; Γ ⊢ v :{l} τ ->
  Σ; Γ ⊢ τ :: *@O ->
  wval v ->
  woval v.
Proof.
  induction 1; intros; try wval_inv;
    kind_inv; simplify_eq;
      try hauto lq: on ctrs: woval, kinding;
      try easy.

  (* TConv *)
  apply_regularity.
  auto_apply; eauto.
  eapply pared_equiv_obliv_preservation; eauto.
  equiv_naive_solver.
Qed.

(** * Canonical forms *)
Ltac canonical_form_solver :=
  inversion 1; intros; subst; eauto;
  type_inv;
  kind_inv;
  try simpl_whnf_equiv;
  simplify_eq;
  eauto 10.

Lemma canonical_form_unit Γ l e :
  val e ->
  Σ; Γ ⊢ e :{l} 𝟙 ->
  e = <{ () }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_abs Γ l1 l2 e τ2 τ1 :
  val e ->
  Σ; Γ ⊢ e :{l1} Π:{l2}τ2, τ1 ->
  exists e' τ, e = <{ \:{l2}τ => e' }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_bool Γ l e :
  val e ->
  Σ; Γ ⊢ e :{l} 𝔹 ->
  exists b, e = <{ b }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_obool Γ l e :
  val e ->
  Σ; Γ ⊢ e :{l} ~𝔹 ->
  exists b, e = <{ [b] }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_prod Γ l e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e :{l} τ1 * τ2 ->
  exists v1 v2, val v1 /\ val v2 /\ e = <{ (v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_sum Γ l e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e :{l} τ1 + τ2 ->
  exists b v τ, val v /\ e = <{ inj@b<τ> v }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_osum Γ l e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e :{l} τ1 ~+ τ2 ->
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
Lemma canonical_form_fold Γ l e X :
  val e ->
  Σ; Γ ⊢ e :{l} gvar X ->
  exists v X', val v /\ e = <{ fold<X'> v }>.
Proof.
  inversion 1; canonical_form_solver.
Qed.

(** * Canonical forms for weak values *)

Lemma canonical_form_weak_unit Γ l e :
  wval e ->
  Σ; Γ ⊢ e :{l} 𝟙 ->
  e = <{ () }> \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_abs Γ l1 l2 e τ2 τ1 :
  wval e ->
  Σ; Γ ⊢ e :{l1} Π:{l2}τ2, τ1 ->
  (exists e' τ, e = <{ \:{l2}τ => e' }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_bool Γ l e :
  wval e ->
  Σ; Γ ⊢ e :{l} 𝔹 ->
  (exists b, e = <{ b }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_obool Γ e :
  wval e ->
  Σ; Γ ⊢ e :{⊥} ~𝔹 ->
  exists b, e = <{ [b] }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_prod Γ l e τ1 τ2 :
  wval e ->
  Σ; Γ ⊢ e :{l} τ1 * τ2 ->
  (exists v1 v2, wval v1 /\ wval v2 /\ e = <{ (v1, v2) }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_sum Γ l e τ1 τ2 :
  wval e ->
  Σ; Γ ⊢ e :{l} τ1 + τ2 ->
  (exists b v τ, wval v /\ e = <{ inj@b<τ> v }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_weak_fold Γ l e X :
  wval e ->
  Σ; Γ ⊢ e :{l} gvar X ->
  (exists v X', wval v /\ e = <{ fold<X'> v }>) \/
  (exists b v1 v2, wval v1 /\ wval v2 /\ e = <{ ~if [b] then v1 else v2 }>).
Proof.
  inversion 1; canonical_form_solver.
Qed.

(** * Progress *)

Ltac ctx_solver :=
  match goal with
  | |- exists _, _ ⊨ _ -->! _ =>
    eexists; solve_ctx
  end.

(** The combined progress theorems for expressions and types. *)
Theorem progress_ :
  (forall Γ e l τ,
      Σ; Γ ⊢ e :{l} τ ->
      Γ = ∅ ->
      wval e \/ exists e', Σ ⊨ e -->! e') /\
  (forall Γ τ κ,
     Σ; Γ ⊢ τ :: κ ->
     Γ = ∅ ->
     κ = <{ *@O }> ->
     otval τ \/ exists τ', Σ ⊨ τ -->! τ').
Proof.
  eapply typing_kinding_mutind; intros; subst;
    (* If a type is not used in the conclusion, the mutual inductive hypothesis
    for it is useless. Remove this hypothesis to avoid slowdown the
    automation. *)
    try match goal with
        | H : context [otval ?τ \/ _] |- val ?e \/ _ =>
          assert_fails contains e τ; clear H
        end;
    (* Try solve the boring cases. *)
    first [ qauto q: on rew: off
                  simp: simpl_map
                  ctrs: wval, otval, step
                  solve: ctx_solver
          (* Take care of the more complex cases involving evaluation context. *)
          | qauto q: on
                  ctrs: wval, otval, step
                  use: canonical_form_weak_abs,
                       canonical_form_weak_bool,
                       canonical_form_weak_obool,
                       canonical_form_weak_prod,
                       canonical_form_weak_sum,
                       canonical_form_weak_fold
                  solve: ctx_solver
          | idtac ].

  (* Injection *)
  - right. intuition; try qauto solve: ctx_solver.
    (* Step to boxed injection *)
    eexists. econstructor; eauto.
    qauto l: on ctrs: otval inv: otval use: wval_val, ovalty_elim, ovalty_intro_alt.

  (* [~case _ of _ | _] *)
  - right. intuition.
    (* Discriminee is value. *)
    + select (_; _ ⊢ _ : _) (fun H => apply canonical_form_osum in H);
        eauto using wval_val.
      simp_hyps.
      select! (otval _) (fun H => use (ovalty_inhabited _ H)).
      hauto ctrs: step.
    (* Discriminee can take a step. *)
    + hauto ctrs: step solve: ctx_solver.

  (* [tape _] *)
  - right. simp_hyps.
    select (wval _ \/ _) (fun H => destruct H);
      [ | hauto ctrs: step solve: ctx_solver ].
    select (wval _) (fun H => eapply wval_woval in H; eauto; sinvert H);
      eauto using step.

  (* [[inj@_<_> _]] *)
  - sfirstorder use: ovalty_elim_alt, val_wval.

  (* [_ + _]. This case is impossible. *)
  - enough (<{ *@P }> ⊑ <{ *@O }>) by easy.
    scongruence use: join_ub_r.

  (* Kinding subsumption *)
  - select kind (fun κ => destruct κ); sintuition use: any_kind_otval.
Qed.

Theorem progress_weak l τ e :
  Σ; ∅ ⊢ e :{l} τ ->
  wval e \/ exists e', Σ ⊨ e -->! e'.
Proof.
  hauto use: progress_.
Qed.

Theorem progress τ e :
  Σ; ∅ ⊢ e :{⊥} τ ->
  val e \/ exists e', Σ ⊨ e -->! e'.
Proof.
  hauto use: progress_, wval_val.
Qed.

Theorem kinding_progress τ :
  Σ; ∅ ⊢ τ :: *@O ->
  otval τ \/ exists τ', Σ ⊨ τ -->! τ'.
Proof.
  hauto use: progress_.
Qed.

End progress.
