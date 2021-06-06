From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.inversion.

(** * Properties *)
(** Lemmas for various definitions. *)

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.

(** ** Weak head normal form *)
(** We only define weak head normal form for types, but may extend it for other
expressions later. *)
Inductive whnf {Σ : gctx} : expr -> Prop :=
| WUnitT : whnf <{ 𝟙 }>
| WBool{l} : whnf <{ 𝔹{l} }>
| WPi τ1 τ2 : whnf <{ Π:τ1, τ2 }>
| WProd τ1 τ2 : whnf <{ τ1 * τ2 }>
| WSum l τ1 τ2 : whnf <{ τ1 +{l} τ2 }>
| WADT X τ :
    Σ !! X = Some (DADT τ) ->
    whnf <{ gvar X }>
.
Arguments whnf : clear implicits.
Hint Constructors whnf : whnf.

(** Type equivalence for the weak head normal form fragments. This relation
always assumes that the two arguments are already in [whnf]. *)
Inductive whnf_equiv {Σ : gctx} : expr -> expr -> Prop :=
| WQUnitT : whnf_equiv <{ 𝟙 }> <{ 𝟙 }>
| WQBool l : whnf_equiv <{ 𝔹{l} }> <{ 𝔹{l} }>
| WQPi τ1 τ2 τ1' τ2' L :
    Σ ⊢ τ1 ≡ τ1' ->
    (forall x, x ∉ L -> Σ ⊢ τ2^x ≡ τ2'^x) ->
    whnf_equiv <{ Π:τ1, τ2 }> <{ Π:τ1', τ2' }>
| WQProd τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 * τ2 }> <{ τ1' * τ2' }>
| WQSum l τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 +{l} τ2 }> <{ τ1' +{l} τ2' }>
| WQADT X : whnf_equiv <{ gvar X }> <{ gvar X }>
| WQInj b τ e τ' e' :
    Σ ⊢ τ ≡ τ' ->
    Σ ⊢ e ≡ e' ->
    whnf_equiv <{ inj@b<τ> e }> <{ inj@b<τ'> e' }>
.
Arguments whnf_equiv : clear implicits.
Hint Constructors whnf_equiv : whnf_equiv.

Lemma otval_whnf Σ ω :
  otval ω ->
  whnf Σ ω.
Proof.
  induction 1; sfirstorder.
Qed.

(** ** Properties of type equivalence  *)
Lemma expr_equiv_step Σ e e' :
  Σ ⊨ e -->! e' ->
  Σ ⊢ e ≡ e'.
Proof.
Admitted.

(* We may weaken it so Γ = ∅. But we need to weaken all theorems depending on
it. *)
Lemma expr_equiv_obliv_type_preserve_ Σ Γ τ τ' κ κ' :
  gctx_wf Σ ->
  Σ; Γ ⊢ τ :: κ ->
  Σ; Γ ⊢ τ' :: κ' ->
  Σ ⊢ τ ≡ τ' ->
  κ ⊑ <{ *@O }> ->
  Σ; Γ ⊢ τ' :: *@O.
Proof.
Admitted.

Lemma expr_equiv_obliv_type_preserve Σ Γ τ τ' κ :
  gctx_wf Σ ->
  Σ; Γ ⊢ τ :: *@O ->
  Σ ⊢ τ ≡ τ' ->
  Σ; Γ ⊢ τ' :: κ ->
  Σ; Γ ⊢ τ' :: *@O.
Proof.
  qauto use: expr_equiv_obliv_type_preserve_ solve: lattice_naive_solver.
Qed.

(** [whnf_equiv] is a faithful fragment of [expr_equiv]. *)
Lemma expr_equiv_iff_whnf_equiv Σ τ1 τ2 :
  whnf Σ τ1 -> whnf Σ τ2 ->
  Σ ⊢ τ1 ≡ τ2 <->
  whnf_equiv Σ τ1 τ2.
Proof.
Admitted.

(** Simplify type equivalence to [whnf_equiv]. Possibly derive contradiction if
two equivalent types in [whnf] have different head. *)
Tactic Notation "simpl_whnf_equiv" "by" tactic3(tac) :=
  match goal with
  | H : _ ⊢ ?τ1 ≡ ?τ2 |- _ =>
    apply expr_equiv_iff_whnf_equiv in H;
    [ sinvert H
    | solve [tac]
    | solve [tac] ]
  end.

Tactic Notation "simpl_whnf_equiv" :=
  simpl_whnf_equiv by eauto using otval_whnf with whnf.


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
