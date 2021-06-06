From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.inversion.
From oadt Require Import lang_oadt.equivalence.

(** * Properties *)
(** Lemmas for various definitions. *)

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.

(** ** Properties of [expr_wf] *)

Lemma open_expr_wf e s :
  expr_wf e ->
  expr_wf s ->
  expr_wf <{ e^s }>.
Proof.
  unfold open. intros H. generalize 0.
  induction H; simpl; intros; try case_decide; eauto with expr_wf.
Qed.

Lemma open_expr_wf_inv e s :
  expr_wf <{ e^s }> ->
  expr_wf s ->
  expr_wf e.
Proof.
  unfold open. generalize 0.
  induction e; simpl; intros; qauto l: on inv: expr_wf ctrs: expr_wf.
Qed.

Lemma open_atom_expr_wf_inv e x :
  expr_wf <{ e^x }> ->
  expr_wf e.
Proof.
  qauto use: open_expr_wf_inv ctrs: expr_wf.
Qed.

Lemma typing_expr_wf Σ Γ e τ :
  Σ; Γ ⊢ e : τ ->
  expr_wf e
with kinding_expr_wf Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  expr_wf τ.
Proof.
  all: destruct 1; eauto with expr_wf;
    simpl_cofin?; qauto l: on ctrs: expr_wf use: open_atom_expr_wf_inv.
Qed.

(** ** Properties of oblivious values *)

Lemma oval_val v :
  oval v ->
  val v.
Proof.
  induction 1; eauto with val.
Qed.

Lemma otval_well_kinded ω Σ Γ :
  otval ω ->
  Σ; Γ ⊢ ω :: *@O.
Proof.
  induction 1; hauto lq: on ctrs: kinding solve: lattice_naive_solver.
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

Lemma ovalty_elim v ω:
  ovalty v ω ->
  oval v /\ otval ω /\ forall Σ Γ, Σ; Γ ⊢ v : ω.
Proof.
  induction 1; hauto lq: on ctrs: oval, ovalty, otval, typing.
Qed.

Lemma ovalty_elim_alt v ω:
  ovalty v ω ->
  val v /\ otval ω /\ forall Σ Γ, Σ; Γ ⊢ v : ω.
Proof.
  hauto use: ovalty_elim, oval_val.
Qed.

Lemma ovalty_intro_alt v ω Σ Γ :
  val v ->
  otval ω ->
  Σ; Γ ⊢ v : ω ->
  ovalty v ω.
Proof.
  intros H. revert ω.
  induction H; inversion 1; intros; subst;
    apply_type_inv;
    simpl_whnf_equiv;
    try hauto lq: on rew: off
              ctrs: ovalty, typing
              use: otval_well_kinded
              solve: equiv_naive_solver.

  (* Case [inj@_<_> _] *)
  repeat match goal with
         | H : _ ⊢ ?ω1 ≡ ?ω2 |- _ =>
           apply otval_uniq in H; try qauto l: on use: ovalty_elim inv: otval
         end.
Qed.

Lemma ovalty_intro v ω Σ Γ :
  oval v ->
  otval ω ->
  Σ; Γ ⊢ v : ω ->
  ovalty v ω.
Proof.
  hauto use: ovalty_intro_alt, oval_val.
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
  - eauto using bot_inv.
Qed.
