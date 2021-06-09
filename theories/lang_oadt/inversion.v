From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.

(** * Inversion Lemmas *)

(** ** Kind inversion  *)
Tactic Notation "kind_inv_solver" "by" tactic3(tac) :=
  match goal with
  | |- _; _ ⊢ ?τ :: _ -> _ => remember τ
  end;
  induction 1; subst; simp_hyps; simplify_eq;
  tac.

Tactic Notation "kind_inv_solver" :=
  kind_inv_solver by (repeat esplit; eauto; lattice_naive_solver).

Lemma kind_inv_pi Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ Π:τ1, τ2 :: κ ->
  κ = <{ *@M }> /\
  exists L κ1 κ2,
    (∀ x, x ∉ L → Σ; (<[x:=τ1]> Γ) ⊢ τ2^x :: κ2) /\
    Σ; Γ ⊢ τ1 :: κ1.
Proof.
  kind_inv_solver by sfirstorder use: top_inv.
Qed.

Lemma kind_inv_bool Σ Γ κ :
  Σ; Γ ⊢ 𝔹 :: κ -> <{ *@P }> ⊑ κ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_prod Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ τ1 * τ2 :: κ ->
  exists κ',
    Σ; Γ ⊢ τ1 :: κ' /\
    Σ; Γ ⊢ τ2 :: κ' /\
    <{ κ' }> ⊑ κ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sum Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ τ1 + τ2 :: κ ->
  <{ *@P }> ⊑ κ /\
  exists κ',
    Σ; Γ ⊢ τ1 :: κ' /\
    Σ; Γ ⊢ τ2 :: κ'.
Proof.
  kind_inv_solver by qauto l: on solve: lattice_naive_solver
                           use: join_ub_r.
Qed.

Lemma kind_inv_osum Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ τ1 ~+ τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  Σ; Γ ⊢ τ1 :: *@O /\
  Σ; Γ ⊢ τ2 :: *@O.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_gvar Σ Γ X κ :
  Σ; Γ ⊢ gvar X :: κ ->
  <{ *@P }> ⊑ κ /\ exists τ, Σ !! X = Some (DADT τ).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_app Σ Γ e1 e2 κ :
  Σ; Γ ⊢ e1 e2 :: κ ->
  <{ *@O }> ⊑ κ /\
  exists X τ e',
    Σ !! X = Some (DOADT τ e') /\
    Σ; Γ ⊢ e2 : τ /\
    e1 = <{ gvar X }>.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ite Σ Γ l e0 τ1 τ2 κ :
  Σ; Γ ⊢ if{l} e0 then τ1 else τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  l = low /\
  Σ; Γ ⊢ e0 : 𝔹 /\
  Σ; Γ ⊢ τ1 :: *@O /\
  Σ; Γ ⊢ τ2 :: *@O.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_let Σ Γ e τ κ :
  Σ; Γ ⊢ let e in τ :: κ ->
  <{ *@O }> ⊑ κ /\
  exists τ' L,
    Σ; Γ ⊢ e : τ' /\
    (forall x, x ∉ L -> Σ; (<[x:=τ']> Γ) ⊢ τ^x :: *@O).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_case Σ Γ l e0 τ1 τ2 κ :
  Σ; Γ ⊢ case{l} e0 of τ1 | τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  l = low /\
  exists τ1' τ2' L1 L2,
    Σ; Γ ⊢ e0 : τ1' + τ2' /\
    (forall x, x ∉ L1 -> Σ; (<[x:=τ1']> Γ) ⊢ τ1^x :: *@O) /\
    (forall x, x ∉ L2 -> Σ; (<[x:=τ2']> Γ) ⊢ τ2^x :: *@O).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_mux Σ Γ e0 e1 e2 κ :
  Σ; Γ ⊢ ~if e0 then e1 else e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sec Σ Γ e κ :
  Σ; Γ ⊢ s𝔹 e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_pair Σ Γ e1 e2 κ :
  Σ; Γ ⊢ (e1, e2) :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_proj Σ Γ b e κ :
  Σ; Γ ⊢ π@b e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_inj Σ Γ l b τ e κ :
  Σ; Γ ⊢ inj{l}@b<τ> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ocase Σ Γ e0 e1 e2 κ :
  Σ; Γ ⊢ ~case e0 of e1 | e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_fold Σ Γ X e κ :
  Σ; Γ ⊢ fold<X> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_unfold Σ Γ X e κ :
  Σ; Γ ⊢ unfold<X> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_abs Σ Γ τ e κ :
  Σ; Γ ⊢ \:τ => e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Tactic Notation "apply_kind_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _ ⊢ Π:_, _ :: _ => tac kind_inv_pi
  | _; _ ⊢ 𝔹 :: _ => tac kind_inv_bool
  | _; _ ⊢ _ _ :: _ => tac kind_inv_app
  | _; _ ⊢ let _ in _ :: _ => tac kind_inv_let
  | _; _ ⊢ _ * _ :: _ => tac kind_inv_prod
  | _; _ ⊢ _ + _ :: _ => tac kind_inv_sum
  | _; _ ⊢ _ ~+ _ :: _ => tac kind_inv_osum
  | _; _ ⊢ gvar _ :: _ => tac kind_inv_gvar
  | _; _ ⊢ ~if _ then _ else _ :: _ => apply kind_inv_mux in H; elim H
  | _; _ ⊢ if{_} _ then _ else _ :: _ => tac kind_inv_ite
  | _; _ ⊢ ~case _ of _ | _ :: _ => apply kind_inv_ocase in H; elim H
  | _; _ ⊢ case{_} _ of _ | _ :: _ => tac kind_inv_case
  | _; _ ⊢ s𝔹 _ :: _ => apply kind_inv_sec in H; elim H
  | _; _ ⊢ (_, _) :: _ => apply kind_inv_pair in H; elim H
  | _; _ ⊢ π@_ _ :: _ => apply kind_inv_proj in H; elim H
  | _; _ ⊢ inj{_}@_<_> _ :: _ => apply kind_inv_inj in H; elim H
  | _; _ ⊢ fold<_> _ :: _ => apply kind_inv_fold in H; elim H
  | _; _ ⊢ unfold<_> _ :: _ => apply kind_inv_unfold in H; elim H
  | _; _ ⊢ \:_ => _ :: _ => apply kind_inv_abs in H; elim H
  end.

Tactic Notation "apply_kind_inv" hyp(H) :=
  apply_kind_inv H by (fun lem => apply lem in H; try simp_hyp H).

Tactic Notation "apply_kind_inv" :=
  do_hyps (fun H => try apply_kind_inv H).

Tactic Notation "apply_kind_inv" "*" :=
  do_hyps (fun H => try dup_hyp H (fun H => apply_kind_inv H)).

(** ** Type inversion *)
Tactic Notation "type_inv_solver" "by" tactic3(tac) :=
  match goal with
  | |- _; _ ⊢ ?e : _ -> _ => remember e
  end;
  induction 1; subst; simp_hyps; simplify_eq;
  tac.

Tactic Notation "type_inv_solver" :=
  type_inv_solver by (repeat esplit; eauto; equiv_naive_solver).

Lemma type_inv_unit Σ Γ τ :
  Σ; Γ ⊢ () : τ ->
  Σ ⊢ τ ≡ 𝟙.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_lit Σ Γ b τ :
  Σ; Γ ⊢ lit b : τ ->
  Σ ⊢ τ ≡ 𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_abs Σ Γ e τ2 τ :
  Σ; Γ ⊢ \:τ2 => e : τ ->
  exists τ1 κ L,
    Σ; Γ ⊢ τ2 :: κ /\
    (forall x, x ∉ L -> Σ; (<[x:=τ2]> Γ) ⊢ e^x : τ1^x) /\
    Σ ⊢ τ ≡ Π:τ2, τ1.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_gvar Σ Γ x τ :
  Σ; Γ ⊢ gvar x : τ ->
  exists τ' e,
    Σ !! x = Some (DFun τ' e) /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_pair Σ Γ e1 e2 τ :
  Σ; Γ ⊢ (e1, e2) : τ ->
  exists τ1 τ2,
    Σ; Γ ⊢ e1 : τ1 /\
    Σ; Γ ⊢ e2 : τ2 /\
    Σ ⊢ τ ≡ τ1 * τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_inj Σ Γ b e τ' τ :
  Σ; Γ ⊢ inj@b<τ'> e : τ ->
  exists τ1 τ2 κ,
    τ' = <{ τ1 + τ2 }> /\
    Σ; Γ ⊢ τ1 + τ2 :: κ /\
    Σ; Γ ⊢ e : ite b τ1 τ2 /\
    Σ ⊢ τ ≡ τ1 + τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_oinj Σ Γ b e τ' τ :
  Σ; Γ ⊢ ~inj@b<τ'> e : τ ->
  exists τ1 τ2,
    τ' = <{ τ1 ~+ τ2 }> /\
    Σ; Γ ⊢ τ1 ~+ τ2 :: *@O /\
    Σ; Γ ⊢ e : ite b τ1 τ2 /\
    Σ ⊢ τ ≡ τ1 ~+ τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_fold Σ Γ X e τ :
  Σ; Γ ⊢ fold<X> e : τ ->
  exists τ',
    Σ; Γ ⊢ e : τ' /\
    Σ !! X = Some (DADT τ') /\
    Σ ⊢ τ ≡ gvar X.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_boxedlit Σ Γ b τ :
  Σ; Γ ⊢ [b] : τ ->
  Σ ⊢ τ ≡ ~𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_boxedinj Σ Γ b v ω τ :
  Σ; Γ ⊢ [inj@b<ω> v] : τ ->
  exists ω1 ω2,
    ω = <{ ω1 ~+ ω2 }> /\
    ovalty <{ [inj@b<ω> v] }> ω /\
    Σ ⊢ τ ≡ ω1 ~+ ω2.
Proof.
  type_inv_solver by hauto lq: on solve: equiv_naive_solver
                           ctrs: ovalty inv: ovalty.
Qed.

Lemma type_inv_case Σ Γ e0 e1 e2 τ :
  Σ; Γ ⊢ case e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' κ L1 L2,
    Σ; Γ ⊢ τ'^e0 :: κ /\
    Σ; Γ ⊢ e0 : τ1 + τ2 /\
    (forall x, x ∉ L1 -> Σ; (<[x:=τ1]> Γ) ⊢ e1^x : τ'^(inl<τ1 + τ2> x)) /\
    (forall x, x ∉ L2 -> Σ; (<[x:=τ2]> Γ) ⊢ e2^x : τ'^(inr<τ1 + τ2> x)) /\
    Σ ⊢ τ ≡ τ'^e0.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_ocase Σ Γ e0 e1 e2 τ :
  Σ; Γ ⊢ ~case e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' L1 L2,
    Σ; Γ ⊢ τ' :: *@O /\
    Σ; Γ ⊢ e0 : τ1 ~+ τ2 /\
    (forall x, x ∉ L1 -> Σ; (<[x:=τ1]> Γ) ⊢ e1^x : τ') /\
    (forall x, x ∉ L2 -> Σ; (<[x:=τ2]> Γ) ⊢ e2^x : τ') /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_case_ Σ Γ l e0 e1 e2 τ :
  Σ; Γ ⊢ case{l} e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' κ L1 L2,
    Σ; Γ ⊢ τ' :: κ /\
    Σ; Γ ⊢ e0 : τ1 +{l} τ2 /\
    (forall x, x ∉ L1 -> exists τ', Σ; (<[x:=τ1]> Γ) ⊢ e1^x : τ') /\
    (forall x, x ∉ L2 -> exists τ', Σ; (<[x:=τ2]> Γ) ⊢ e2^x : τ') /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver by (repeat (esplit; eauto); equiv_naive_solver).
Qed.

Lemma type_inv_prod Σ Γ τ1 τ2 τ :
  Σ; Γ ⊢ τ1 * τ2 : τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_sum Σ Γ l τ1 τ2 τ :
  Σ; Γ ⊢ τ1 +{l} τ2 : τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_app Σ Γ e1 e2 τ :
  Σ; Γ ⊢ e1 e2 : τ ->
  exists τ1 τ2,
    Σ; Γ ⊢ e1 : Π:τ2, τ1 /\
    Σ; Γ ⊢ e2 : τ2 /\
    Σ ⊢ τ ≡ τ1^e2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_let Σ Γ e1 e2 τ :
  Σ; Γ ⊢ let e1 in e2 : τ ->
  exists τ1 τ2 L,
    Σ; Γ ⊢ e1 : τ1 /\
    (forall x, x ∉ L -> Σ; (<[x:=τ1]> Γ) ⊢ e2^x : τ2^x) /\
    Σ ⊢ τ ≡ τ2^e1.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_sec Σ Γ e τ :
  Σ; Γ ⊢ s𝔹 e : τ ->
  Σ; Γ ⊢ e : 𝔹 /\
  Σ ⊢ τ ≡ ~𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_ite Σ Γ e0 e1 e2 τ :
  Σ; Γ ⊢ if e0 then e1 else e2 : τ ->
  exists τ' κ,
    Σ; Γ ⊢ e0 : 𝔹 /\
    Σ; Γ ⊢ e1 : τ'^(lit true) /\
    Σ; Γ ⊢ e2 : τ'^(lit false) /\
    Σ; Γ ⊢ τ'^e0 :: κ /\
    Σ ⊢ τ ≡ τ'^e0.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_mux Σ Γ e0 e1 e2 τ :
  Σ; Γ ⊢ ~if e0 then e1 else e2 : τ ->
  exists τ',
    Σ; Γ ⊢ e0 : ~𝔹 /\
    Σ; Γ ⊢ e1 : τ' /\
    Σ; Γ ⊢ e2 : τ' /\
    Σ; Γ ⊢ τ' :: *@O /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_proj Σ Γ b e τ :
  Σ; Γ ⊢ π@b e : τ ->
  exists τ1 τ2,
    Σ; Γ ⊢ e : τ1 * τ2 /\
    Σ ⊢ τ ≡ ite b τ1 τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_unfold Σ Γ X e τ :
  Σ; Γ ⊢ unfold<X> e : τ ->
  exists τ',
    Σ !! X = Some (DADT τ') /\
    Σ; Γ ⊢ e : gvar X /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Tactic Notation "apply_type_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _ ⊢ () : _ => tac type_inv_unit
  | _; _ ⊢ lit _ : _ => tac type_inv_lit
  | _; _ ⊢ gvar _ : _ => tac type_inv_gvar
  | _; _ ⊢ \:_ => _ : _ => tac type_inv_abs
  | _; _ ⊢ _ _ : _ => tac type_inv_app
  | _; _ ⊢ let _ in _ : _ => tac type_inv_let
  | _; _ ⊢ (_, _) : _ => tac type_inv_pair
  | _; _ ⊢ s𝔹 _ : _ => tac type_inv_sec
  | _; _ ⊢ π@_ _ : _ => tac type_inv_proj
  | _; _ ⊢ ~inj@_<_> _ : _ => tac type_inv_oinj
  | _; _ ⊢ inj@_<_> _ : _ => tac type_inv_inj
  | _; _ ⊢ ~if _ then _ else _ : _ => tac type_inv_mux
  | _; _ ⊢ if _ then _ else _ : _ => tac type_inv_ite
  | _; _ ⊢ ~case _ of _ | _ : _ => tac type_inv_ocase
  | _; _ ⊢ case _ of _ | _ : _ => tac type_inv_case
  | _; _ ⊢ case{_} _ of _ | _ : _ => tac type_inv_case_
  | _; _ ⊢ fold<_> _ : _ => tac type_inv_fold
  | _; _ ⊢ unfold<_> _ : _ => tac type_inv_unfold
  | _; _ ⊢ [_] : _ => tac type_inv_boxedlit
  | _; _ ⊢ [inj@_<_> _] : _ => tac type_inv_boxedinj
  | _; _ ⊢ _ * _ : _ => apply type_inv_prod in H; elim H
  | _; _ ⊢ _ +{_} _ : _ => apply type_inv_sum in H; elim H
  end.

Tactic Notation "apply_type_inv" hyp(H) :=
  apply_type_inv H by (fun lem => apply lem in H; try simp_hyp H).

Tactic Notation "apply_type_inv" :=
  do_hyps (fun H => try apply_type_inv H).

Tactic Notation "apply_type_inv" "*" :=
  do_hyps (fun H => try dup_hyp H (fun H => apply_type_inv H)).
