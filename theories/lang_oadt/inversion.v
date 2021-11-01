(** Typing and kinding inversion lemmas. *)
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.equivalence.

Import syntax.notations.
Import semantics.notations.
Import typing.notations.
Import equivalence.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

Section inversion.

Context (Σ : gctx).

#[local]
Set Default Proof Using "Type".

(** * Kind inversion  *)
Tactic Notation "kind_inv_solver" "by" tactic3(tac) :=
  match goal with
  | |- _ ⊢ ?τ :: _ -> _ => remember τ
  end;
  induction 1; subst; simp_hyps; simplify_eq;
  tac.

Ltac kind_inv_solver :=
  kind_inv_solver by (repeat esplit; eauto;
                      lattice_naive_solver by eauto using top_inv, join_ub_r).

Lemma kind_inv_pi Γ l τ1 τ2 κ :
  Γ ⊢ Π:{l}τ1, τ2 :: κ ->
  κ = <{ *@M }> /\
  exists L κ1 κ2,
    (∀ x, x ∉ L → (<[x:=(l, τ1)]> Γ) ⊢ τ2^x :: κ2) /\
    Γ ⊢ τ1 :: κ1.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_bool Γ κ :
  Γ ⊢ 𝔹 :: κ -> <{ *@P }> ⊑ κ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_prod Γ τ1 τ2 κ :
  Γ ⊢ τ1 * τ2 :: κ ->
  exists κ',
    Γ ⊢ τ1 :: κ' /\
    Γ ⊢ τ2 :: κ' /\
    <{ κ' }> ⊑ κ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sum Γ τ1 τ2 κ :
  Γ ⊢ τ1 + τ2 :: κ ->
  <{ *@P }> ⊑ κ /\
  exists κ',
    Γ ⊢ τ1 :: κ' /\
    Γ ⊢ τ2 :: κ'.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_osum Γ τ1 τ2 κ :
  Γ ⊢ τ1 ~+ τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  Γ ⊢ τ1 :: *@O /\
  Γ ⊢ τ2 :: *@O.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_gvar Γ X κ :
  Γ ⊢ gvar X :: κ ->
  <{ *@P }> ⊑ κ /\ exists τ, Σ !! X = Some (DADT τ).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_tapp Γ X e κ :
  Γ ⊢ X@e :: κ ->
  <{ *@O }> ⊑ κ /\
  exists τ e',
    Σ !! X = Some (DOADT τ e') /\
    Γ ⊢ e :{⊥} τ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ite Γ l e0 τ1 τ2 κ :
  Γ ⊢ if{l} e0 then τ1 else τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  l = LPub /\
  Γ ⊢ e0 :{⊥} 𝔹 /\
  Γ ⊢ τ1 :: *@O /\
  Γ ⊢ τ2 :: *@O.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_let Γ e τ κ :
  Γ ⊢ let e in τ :: κ ->
  <{ *@O }> ⊑ κ /\
  exists τ' L,
    Γ ⊢ e :{⊥} τ' /\
    (forall x, x ∉ L -> <[x:=(⊥, τ')]> Γ ⊢ τ^x :: *@O).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_case Γ l e0 τ1 τ2 κ :
  Γ ⊢ case{l} e0 of τ1 | τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  l = LPub /\
  exists τ1' τ2' L1 L2,
    Γ ⊢ e0 :{⊥} τ1' + τ2' /\
    (forall x, x ∉ L1 -> <[x:=(⊥, τ1')]> Γ ⊢ τ1^x :: *@O) /\
    (forall x, x ∉ L2 -> <[x:=(⊥, τ2')]> Γ ⊢ τ2^x :: *@O).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_app Γ e1 e2 κ :
  Γ ⊢ e1 e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_oite Γ e0 e1 e2 κ :
  Γ ⊢ ~if e0 then e1 else e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_mux Γ e0 e1 e2 κ :
  Γ ⊢ mux e0 e1 e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sec Γ e κ :
  Γ ⊢ s𝔹 e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_pair Γ e1 e2 κ :
  Γ ⊢ (e1, e2) :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_proj Γ b e κ :
  Γ ⊢ π@b e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_inj Γ l b τ e κ :
  Γ ⊢ inj{l}@b<τ> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ocase Γ e0 e1 e2 κ :
  Γ ⊢ ~case e0 of e1 | e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_fold Γ X e κ :
  Γ ⊢ fold<X> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_unfold Γ X e κ :
  Γ ⊢ unfold<X> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_abs Γ l τ e κ :
  Γ ⊢ \:{l}τ => e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_tape Γ e κ :
  Γ ⊢ tape e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

(** * Type inversion *)
Tactic Notation "type_inv_solver" "by" tactic3(tac) :=
  match goal with
  | |- _ ⊢ ?e : _ -> _ => remember e
  end;
  induction 1; subst; simp_hyps; simplify_eq;
  tac.

Ltac type_inv_solver :=
  type_inv_solver by (repeat (eauto; esplit);
                      try first [ goal_is (_ ≡ _); equiv_naive_solver
                                | try select kind (fun k => clear dependent k);
                                  lattice_naive_solver
                                    by eauto using (top_inv (A:=bool)) ]).

Lemma type_inv_prod Γ l τ1 τ2 τ :
  Γ ⊢ τ1 * τ2 :{l} τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_sum Γ l l' τ1 τ2 τ :
  Γ ⊢ τ1 +{l} τ2 :{l'} τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_tapp Γ l X e τ :
  Γ ⊢ X@e :{l} τ -> False.
Proof.
  type_inv_solver.
Qed.

(** From now on the proofs rely on the well-formedness of global context. *)
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "Hwf".

Lemma type_inv_unit Γ l τ :
  Γ ⊢ () :{l} τ ->
  τ ≡ <{ 𝟙 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_lit Γ l b τ :
  Γ ⊢ lit b :{l} τ ->
  τ ≡ <{ 𝔹 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_abs Γ l1 l2 e τ2 τ :
  Γ ⊢ \:{l2}τ2 => e :{l1} τ ->
  exists l1' τ1 κ L,
    Γ ⊢ τ2 :: κ /\
    (forall x, x ∉ L -> <[x:=(l2, τ2)]> Γ ⊢ e^x :{l1'} τ1^x) /\
    l1' ⊑ l1 /\
    τ ≡ <{ Π:{l2}τ2, τ1 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_gvar Γ l x τ :
  Γ ⊢ gvar x :{l} τ ->
  exists l' τ' e,
    Σ !! x = Some (DFun (l', τ') e) /\
    l' ⊑ l /\
    τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_pair Γ l e1 e2 τ :
  Γ ⊢ (e1, e2) :{l} τ ->
  exists l1 l2 τ1 τ2,
    Γ ⊢ e1 :{l1} τ1 /\
    Γ ⊢ e2 :{l2} τ2 /\
    l1 ⊔ l2 ⊑ l /\
    τ ≡ <{ τ1 * τ2 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_inj Γ l b e τ' τ :
  Γ ⊢ inj@b<τ'> e :{l} τ ->
  exists l' τ1 τ2 κ,
    τ' = <{ τ1 + τ2 }> /\
    Γ ⊢ τ1 + τ2 :: κ /\
    Γ ⊢ e :{l'} ite b τ1 τ2 /\
    l' ⊑ l /\
    τ ≡ <{ τ1 + τ2 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_oinj Γ l b e τ' τ :
  Γ ⊢ ~inj@b<τ'> e :{l} τ ->
  exists τ1 τ2,
    τ' = <{ τ1 ~+ τ2 }> /\
    Γ ⊢ τ1 ~+ τ2 :: *@O /\
    Γ ⊢ e :{⊥} ite b τ1 τ2 /\
    τ ≡ <{ τ1 ~+ τ2 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_fold Γ l X e τ :
  Γ ⊢ fold<X> e :{l} τ ->
  exists l' τ',
    Γ ⊢ e :{l'} τ' /\
    Σ !! X = Some (DADT τ') /\
    l' ⊑ l /\
    τ ≡ <{ gvar X }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_boxedlit Γ l b τ :
  Γ ⊢ [b] :{l} τ ->
  τ ≡ <{ ~𝔹 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_boxedinj Γ l b v ω τ :
  Γ ⊢ [inj@b<ω> v] :{l} τ ->
  exists ω1 ω2,
    ω = <{ ω1 ~+ ω2 }> /\
    ovalty <{ [inj@b<ω> v] }> ω /\
    τ ≡ <{ ω1 ~+ ω2 }>.
Proof.
  type_inv_solver by hauto lq: on ctrs: ovalty inv: ovalty
                           solve: equiv_naive_solver.
Qed.

Lemma type_inv_case Γ l e0 e1 e2 τ :
  Γ ⊢ case e0 of e1 | e2 :{l} τ ->
  exists l0 l1 l2 τ1 τ2 τ' κ L1 L2,
    Γ ⊢ τ'^e0 :: κ /\
    Γ ⊢ e0 :{l0} τ1 + τ2 /\
    (forall x, x ∉ L1 -> <[x:=(l0, τ1)]> Γ ⊢ e1^x :{l1} τ'^(inl<τ1 + τ2> x)) /\
    (forall x, x ∉ L2 -> <[x:=(l0, τ2)]> Γ ⊢ e2^x :{l2} τ'^(inr<τ1 + τ2> x)) /\
    l0 ⊔ l1 ⊔ l2 ⊑ l /\
    τ ≡ <{ τ'^e0 }>.
Proof.
  type_inv_solver.

  all : intros;
    lazymatch goal with
    | H : _; _ ⊢ ?τ :: _ |- _ =>
      rewrite (open_lc_intro τ) by eauto using kinding_lc
    end; eauto; equiv_naive_solver.
Qed.

Lemma type_inv_ocase Γ l e0 e1 e2 τ :
  Γ ⊢ ~case e0 of e1 | e2 :{l} τ ->
  exists l1 l2 τ1 τ2 τ' κ L1 L2,
    Γ ⊢ τ' :: κ /\
    Γ ⊢ e0 :{⊥} τ1 ~+ τ2 /\
    (forall x, x ∉ L1 -> <[x:=(⊥, τ1)]> Γ ⊢ e1^x :{l1} τ') /\
    (forall x, x ∉ L2 -> <[x:=(⊥, τ2)]> Γ ⊢ e2^x :{l2} τ') /\
    τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_case_ Γ l l' e0 e1 e2 τ :
  Γ ⊢ case{l} e0 of e1 | e2 :{l'} τ ->
  exists l0 l1 l2 τ1 τ2 τ' κ L1 L2,
    Γ ⊢ τ' :: κ /\
    Γ ⊢ e0 :{l0} τ1 +{l} τ2 /\
    (forall x, x ∉ L1 -> exists τ', <[x:=(l0, τ1)]> Γ ⊢ e1^x :{l1} τ') /\
    (forall x, x ∉ L2 -> exists τ', <[x:=(l0, τ2)]> Γ ⊢ e2^x :{l2} τ') /\
    τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_app Γ l1 e1 e2 τ :
  Γ ⊢ e1 e2 :{l1} τ ->
  exists l1' l2 τ1 τ2,
    Γ ⊢ e1 :{l1'} Π:{l2}τ2, τ1 /\
    Γ ⊢ e2 :{l2} τ2 /\
    l1' ⊑ l1 /\
    τ ≡ <{ τ1^e2 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_let Γ l e1 e2 τ :
  Γ ⊢ let e1 in e2 :{l} τ ->
  exists l1 l2 τ1 τ2 L,
    Γ ⊢ e1 :{l1} τ1 /\
    (forall x, x ∉ L -> <[x:=(l1, τ1)]> Γ ⊢ e2^x :{l2} τ2^x) /\
    l1 ⊔ l2 ⊑ l /\
    τ ≡ <{ τ2^e1 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_sec Γ l e τ :
  Γ ⊢ s𝔹 e :{l} τ ->
  exists l',
    Γ ⊢ e :{l'} 𝔹 /\
    l' ⊑ l /\
    τ ≡ <{ ~𝔹 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_ite Γ l e0 e1 e2 τ :
  Γ ⊢ if e0 then e1 else e2 :{l} τ ->
  exists l0 l1 l2 τ',
    Γ ⊢ e0 :{l0} 𝔹 /\
    Γ ⊢ e1 :{l1} τ'^(lit true) /\
    Γ ⊢ e2 :{l2} τ'^(lit false) /\
    l0 ⊔ l1 ⊔ l2 ⊑ l /\
    τ ≡ <{ τ'^e0 }>.
Proof.
  type_inv_solver.

  all :
    lazymatch goal with
    | H : _; _ ⊢ _ : ?τ |- _ =>
      rewrite (open_lc_intro τ) by eauto using typing_type_lc
    end; eauto; try equiv_naive_solver.
Qed.

Lemma type_inv_oite Γ l e0 e1 e2 τ :
  Γ ⊢ ~if e0 then e1 else e2 :{l} τ ->
  exists l1 l2 τ' κ,
    Γ ⊢ e0 :{⊥} ~𝔹 /\
    Γ ⊢ e1 :{l1} τ' /\
    Γ ⊢ e2 :{l2} τ' /\
    Γ ⊢ τ' :: κ /\
    l = ⊤ /\
    τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_mux Γ l e0 e1 e2 τ :
  Γ ⊢ mux e0 e1 e2 :{l} τ ->
  exists τ',
    Γ ⊢ e0 :{⊥} ~𝔹 /\
    Γ ⊢ e1 :{⊥} τ' /\
    Γ ⊢ e2 :{⊥} τ' /\
    Γ ⊢ τ' :: *@O /\
    τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_proj Γ l b e τ :
  Γ ⊢ π@b e :{l} τ ->
  exists l' τ1 τ2,
    Γ ⊢ e :{l'} τ1 * τ2 /\
    l' ⊑ l /\
    τ ≡ <{ ite b τ1 τ2 }>.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_unfold Γ l X e τ :
  Γ ⊢ unfold<X> e :{l} τ ->
  exists l' τ',
    Σ !! X = Some (DADT τ') /\
    Γ ⊢ e :{l'} gvar X /\
    l' ⊑ l /\
    τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_tape Γ l e τ :
  Γ ⊢ tape e :{l} τ ->
  exists l' τ',
    Γ ⊢ e :{l'} τ' /\
    Γ ⊢ τ' :: *@O /\
    τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

End inversion.

(** * Tactics *)

Tactic Notation "kind_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _ ⊢ Π:{_}_, _ :: _ => tac kind_inv_pi
  | _; _ ⊢ 𝔹 :: _ => tac kind_inv_bool
  | _; _ ⊢ _@_ :: _ => tac kind_inv_tapp
  | _; _ ⊢ let _ in _ :: _ => tac kind_inv_let
  | _; _ ⊢ _ * _ :: _ => tac kind_inv_prod
  | _; _ ⊢ _ + _ :: _ => tac kind_inv_sum
  | _; _ ⊢ _ ~+ _ :: _ => tac kind_inv_osum
  | _; _ ⊢ gvar _ :: _ => tac kind_inv_gvar
  | _; _ ⊢ _ _ :: _ => apply kind_inv_app in H; elim H
  | _; _ ⊢ ~if _ then _ else _ :: _ => apply kind_inv_oite in H; elim H
  | _; _ ⊢ if{_} _ then _ else _ :: _ => tac kind_inv_ite
  | _; _ ⊢ ~case _ of _ | _ :: _ => apply kind_inv_ocase in H; elim H
  | _; _ ⊢ case{_} _ of _ | _ :: _ => tac kind_inv_case
  | _; _ ⊢ s𝔹 _ :: _ => apply kind_inv_sec in H; elim H
  | _; _ ⊢ (_, _) :: _ => apply kind_inv_pair in H; elim H
  | _; _ ⊢ π@_ _ :: _ => apply kind_inv_proj in H; elim H
  | _; _ ⊢ inj{_}@_<_> _ :: _ => apply kind_inv_inj in H; elim H
  | _; _ ⊢ fold<_> _ :: _ => apply kind_inv_fold in H; elim H
  | _; _ ⊢ unfold<_> _ :: _ => apply kind_inv_unfold in H; elim H
  | _; _ ⊢ \:{_}_ => _ :: _ => apply kind_inv_abs in H; elim H
  | _; _ ⊢ mux _ _ _ :: _ => apply kind_inv_mux in H; elim H
  | _; _ ⊢ tape _ :: _ => apply kind_inv_tape in H; elim H
  end.

Tactic Notation "kind_inv" hyp(H) :=
  kind_inv H by (fun lem => apply lem in H; try simp_hyp H).

Tactic Notation "kind_inv" :=
  do_hyps (fun H => try kind_inv H).

Tactic Notation "kind_inv" "*" :=
  do_hyps (fun H => try dup_hyp H (fun H => kind_inv H)).

Tactic Notation "type_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _ ⊢ () : _ => tac type_inv_unit
  | _; _ ⊢ lit _ : _ => tac type_inv_lit
  | _; _ ⊢ gvar _ : _ => tac type_inv_gvar
  | _; _ ⊢ \:{_}_ => _ : _ => tac type_inv_abs
  | _; _ ⊢ _ _ : _ => tac type_inv_app
  | _; _ ⊢ let _ in _ : _ => tac type_inv_let
  | _; _ ⊢ (_, _) : _ => tac type_inv_pair
  | _; _ ⊢ s𝔹 _ : _ => tac type_inv_sec
  | _; _ ⊢ π@_ _ : _ => tac type_inv_proj
  | _; _ ⊢ ~inj@_<_> _ : _ => tac type_inv_oinj
  | _; _ ⊢ inj@_<_> _ : _ => tac type_inv_inj
  | _; _ ⊢ ~if _ then _ else _ : _ => tac type_inv_oite
  | _; _ ⊢ if _ then _ else _ : _ => tac type_inv_ite
  | _; _ ⊢ ~case _ of _ | _ : _ => tac type_inv_ocase
  | _; _ ⊢ case _ of _ | _ : _ => tac type_inv_case
  | _; _ ⊢ case{_} _ of _ | _ : _ => tac type_inv_case_
  | _; _ ⊢ fold<_> _ : _ => tac type_inv_fold
  | _; _ ⊢ unfold<_> _ : _ => tac type_inv_unfold
  | _; _ ⊢ mux _ _ _ : _ => tac type_inv_mux
  | _; _ ⊢ tape _ : _ => tac type_inv_tape
  | _; _ ⊢ [_] : _ => tac type_inv_boxedlit
  | _; _ ⊢ [inj@_<_> _] : _ => tac type_inv_boxedinj
  | _; _ ⊢ _ * _ : _ => apply type_inv_prod in H; elim H
  | _; _ ⊢ _ +{_} _ : _ => apply type_inv_sum in H; elim H
  | _; _ ⊢ _@_ : _ => apply type_inv_tapp in H; elim H
  end.

Tactic Notation "type_inv" hyp(H) :=
  type_inv H by (fun lem => apply lem in H; try simp_hyp H);
  try lazymatch goal with
      | |- gctx_wf _ => assumption
      end.

Tactic Notation "type_inv" :=
  do_hyps (fun H => try type_inv H).

Tactic Notation "type_inv" "*" :=
  do_hyps (fun H => try dup_hyp H (fun H => type_inv H)).
