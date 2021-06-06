From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.inversion.

(** * Expression Equivalence *)
(** Lemmas for expression equivalence. *)

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

Lemma otval_whnf Σ ω :
  otval ω ->
  whnf Σ ω.
Proof.
  induction 1; sfirstorder.
Qed.

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
