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

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

(** ** Properties of values *)

Lemma oval_val v :
  oval v ->
  val v.
Proof.
  induction 1; eauto using val.
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

Lemma ovalty_elim_alt v ω:
  ovalty v ω ->
  val v /\ otval ω /\ forall Σ Γ, Σ; Γ ⊢ v :{⊥} ω.
Proof.
  hauto use: ovalty_elim, oval_val.
Qed.

Lemma ovalty_intro_alt v ω l Σ Γ :
  gctx_wf Σ ->
  val v ->
  otval ω ->
  Σ; Γ ⊢ v :{l} ω ->
  ovalty v ω.
Proof.
  intros Hwf H. revert ω l.
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

Lemma ovalty_intro v ω l Σ Γ :
  gctx_wf Σ ->
  oval v ->
  otval ω ->
  Σ; Γ ⊢ v :{l} ω ->
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

Lemma wval_val Σ Γ τ v :
  Σ; Γ ⊢ v :{⊥} τ ->
  wval v ->
  val v.
Proof.
  remember ⊥.
  induction 1; subst; intros;
    try match goal with
        | H : wval ?v |- _ => head_constructor v; sinvert H
        end; simplify_eq; eauto using val, (bot_inv (A:=bool)).
  select (⊥ = _ ⊔ _) (fun H => symmetry in H; apply join_bot_iff in H).
  hauto ctrs: val.
Qed.

Lemma val_wval v :
  val v ->
  wval v.
Proof.
  induction 1; eauto using wval.
Qed.

Lemma woval_otval Σ Γ v l τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ v :{l} τ ->
  woval v ->
  exists ω, Σ; Γ ⊢ v :{l} ω /\ otval ω /\ Σ ⊢ ω ≡ τ.
Proof.
  intros Hwf.
  induction 1; intros Hv;
    try lazymatch type of Hv with
        | woval ?e => head_constructor e; sinvert Hv
        end; simp_hyps;
      try solve [ repeat esplit; eauto;
                  try lazymatch goal with
                      | |- _; _ ⊢ _ : _ =>
                        repeat (econstructor;
                                eauto using otval_well_kinded;
                                try equiv_naive_solver)
                      | |- _ ⊢ _ ≡ _ => equiv_naive_solver
                      | |- otval _ => eauto using otval
                      end ].

  (* Product *)
  repeat esplit.
  econstructor; eauto using otval_well_kinded; try equiv_naive_solver.
  eauto using otval.
  apply_pared_equiv_congr; eauto with lc.
Qed.

Lemma woval_wval v :
  woval v ->
  wval v.
Proof.
  induction 1; eauto using wval.
Qed.

Lemma oval_woval v :
  oval v ->
  woval v.
Proof.
  induction 1; eauto using woval.
Qed.
