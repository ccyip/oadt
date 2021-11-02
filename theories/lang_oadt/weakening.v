From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.

Import syntax.notations.
Import typing.notations.

(** * Weakening lemmas  *)

Lemma pared_weakening Σ e e' :
  Σ ⊢ e ⇛ e' ->
  forall Σ', Σ ⊆ Σ' ->
        Σ' ⊢ e ⇛ e'.
Proof.
  induction 1; intros;
    econstructor; eauto; qauto use: lookup_weaken.
Qed.

Lemma pared_equiv_weakening Σ e e' :
  Σ ⊢ e ≡ e' ->
  forall Σ', Σ ⊆ Σ' ->
        Σ' ⊢ e ≡ e'.
Proof.
  induction 1; intros; qauto use: pared_equiv, pared_weakening.
Qed.

Lemma weakening_ Σ :
  (forall Γ e l τ,
    Σ; Γ ⊢ e :{l} τ ->
    forall Σ' Γ',
      Σ ⊆ Σ' ->
      Γ ⊆ Γ' ->
      Σ'; Γ' ⊢ e :{l} τ) /\
  (forall Γ τ κ,
    Σ; Γ ⊢ τ :: κ ->
    forall Σ' Γ',
      Σ ⊆ Σ' ->
      Γ ⊆ Γ' ->
      Σ'; Γ' ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind; intros; subst;
    try qauto l: on ctrs: typing, kinding;
    try qauto l: on use: lookup_weaken ctrs: typing, kinding;
    try qauto l: on use: insert_mono ctrs: typing, kinding;
    (* For the [case]/[~case] cases and the [TConv] case. *)
    econstructor; eauto using insert_mono; qauto use: pared_equiv_weakening.
Qed.

Lemma weakening Σ Γ Σ' Γ' e l τ :
  Σ; Γ ⊢ e :{l} τ ->
  Σ ⊆ Σ' ->
  Γ ⊆ Γ' ->
  Σ'; Γ' ⊢ e :{l} τ.
Proof.
  hauto use: weakening_.
Qed.

Lemma kinding_weakening Σ Γ Σ' Γ' τ κ :
  Σ; Γ ⊢ τ :: κ ->
  Σ ⊆ Σ' ->
  Γ ⊆ Γ' ->
  Σ'; Γ' ⊢ τ :: κ.
Proof.
  hauto use: weakening_.
Qed.

Lemma weakening_empty Σ Γ e l τ :
  Σ; ∅ ⊢ e :{l} τ ->
  Σ; Γ ⊢ e :{l} τ.
Proof.
  eauto using weakening, map_empty_subseteq.
Qed.

Lemma kinding_weakening_empty Σ Γ τ κ :
  Σ; ∅ ⊢ τ :: κ ->
  Σ; Γ ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, map_empty_subseteq.
Qed.

Lemma weakening_insert Σ Γ e l τ τ' x :
  Σ; Γ ⊢ e :{l} τ ->
  x ∉ dom aset Γ ->
  Σ; <[x:=τ']>Γ ⊢ e :{l} τ.
Proof.
  eauto using weakening, insert_fresh_subseteq.
Qed.

Lemma kinding_weakening_insert Σ Γ τ τ' κ x :
  Σ; Γ ⊢ τ :: κ ->
  x ∉ dom aset Γ ->
  Σ; <[x:=τ']>Γ ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, insert_fresh_subseteq.
Qed.
