From oadt Require Import prelude.
From oadt Require Import lang_oadt.infrastructure.

(** * Properties *)
(** Lemmas for various definitions. *)

Module M (atom_sig : AtomSig).

Include infrastructure.M atom_sig.
Import syntax_notations.
Import semantics_notations.
Import typing_notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.

(** This lemma is equivalent to [SCtx] constructor, but more friendly for
automation. *)
Lemma SCtx_intro {Σ} ℇ e e' E E' :
    Σ ⊨ e -->! e' ->
    ℇ e = E ->
    ℇ e' = E' ->
    ectx ℇ ->
    Σ ⊨ E -->! E'.
Proof.
  hauto ctrs: step.
Qed.

(** [kind] forms a [SemiLattice].  *)
Instance kind_semilattice : SemiLattice kind.
Proof.
  split; try reflexivity; repeat intros []; auto.
Qed.

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
always assumes that the two type arguments are already in [whnf]. *)
Inductive whnf_equiv {Σ : gctx} : expr -> expr -> Prop :=
| WEqUnitT : whnf_equiv <{ 𝟙 }> <{ 𝟙 }>
| WEqBool l : whnf_equiv <{ 𝔹{l} }> <{ 𝔹{l} }>
| WEqPi τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ Π:τ1, τ2 }> <{ Π:τ1', τ2' }>
| WEqProd τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 * τ2 }> <{ τ1' * τ2' }>
| WEqSum l τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 +{l} τ2 }> <{ τ1' +{l} τ2' }>
| WEqADT X : whnf_equiv <{ gvar X }> <{ gvar X }>
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

Instance expr_equiv_is_equiv Σ : Equivalence (expr_equiv Σ).
Proof.
Admitted.

(** [whnf_equiv] is a faithful fragment of [expr_equiv]. *)
Lemma expr_equiv_iff_whnf_equiv Σ τ1 τ2 :
  whnf Σ τ1 -> whnf Σ τ2 ->
  Σ ⊢ τ1 ≡ τ2 <->
  whnf_equiv Σ τ1 τ2.
Proof.
Admitted.

(* NOTE: Be aware of circular proofs! In case we need [gctx_wf] as a side
condition, as we need this lemma to prove [gctx_wf] for well-typed global
context. *)
Lemma expr_equiv_weakening Σ τ τ' :
  Σ ⊢ τ ≡ τ' ->
  forall Σ', Σ ⊆ Σ' ->
        Σ' ⊢ τ ≡ τ'.
Admitted.

(* Some side conditions may be needed for the next few lemmas. *)

Lemma expr_equiv_step Σ e e' :
  Σ ⊨ e -->! e' ->
  Σ ⊢ e ≡ e'.
Proof.
Admitted.

Lemma expr_equiv_subst Σ τ τ' e e' x :
  Σ ⊢ τ ≡ τ' ->
  Σ ⊢ e ≡ e' ->
  Σ ⊢ {x↦e}τ ≡ {x↦e'}τ'.
Proof.
Admitted.

Lemma expr_equiv_open_atom Σ τ1 τ2 x :
  Σ ⊢ τ1 ≡ τ2 ->
  Σ ⊢ τ1^x ≡ τ2^x.
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

Lemma expr_equiv_rename Σ τ τ' x y :
  Σ ⊢ τ ≡ τ' ->
  Σ ⊢ {x↦y}τ ≡ {x↦y}τ'.
Proof.
  qauto use: expr_equiv_subst solve: equiv_naive_solver.
Qed.

Lemma expr_equiv_subst1 Σ τ τ' x s :
  Σ ⊢ τ ≡ τ' ->
  Σ ⊢ {x↦s}τ ≡ {x↦s}τ'.
Proof.
  qauto use: expr_equiv_subst solve: equiv_naive_solver.
Qed.

Lemma expr_equiv_subst2 Σ τ x e e' :
  Σ ⊢ e ≡ e' ->
  Σ ⊢ {x↦e}τ ≡ {x↦e'}τ.
Proof.
  qauto use: expr_equiv_subst solve: equiv_naive_solver.
Qed.

Lemma expr_equiv_open1 Σ τ1 τ2 e :
  Σ ⊢ τ1 ≡ τ2 ->
  Σ ⊢ τ1^e ≡ τ2^e.
Proof.
  destruct (exist_fresh (fv τ1 ∪ fv τ2)) as [x ?].
  erewrite (subst_intro τ1 e x) by fast_set_solver!!.
  erewrite (subst_intro τ2 e x) by fast_set_solver!!.
  eauto using expr_equiv_subst1, expr_equiv_open_atom.
Qed.

Lemma expr_equiv_open2 Σ τ e1 e2 :
  Σ ⊢ e1 ≡ e2 ->
  Σ ⊢ τ^e1 ≡ τ^e2.
Proof.
  destruct (exist_fresh (fv τ)) as [x ?].
  erewrite (subst_intro τ e1 x) by eassumption.
  erewrite (subst_intro τ e2 x) by eassumption.
  eauto using expr_equiv_subst2.
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
  l = ⊥ /\
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
  l = ⊥ /\
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

Lemma type_inv_inj Σ Γ l b e τ' τ :
  Σ; Γ ⊢ inj{l}@b<τ'> e : τ ->
  exists τ1 τ2,
    τ' = <{ τ1 +{l} τ2 }> /\
    Σ; Γ ⊢ τ1 +{l} τ2 :: ite l *@O *@P /\
    Σ; Γ ⊢ e : ite b τ1 τ2 /\
    Σ ⊢ τ ≡ τ1 +{l} τ2.
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
    oval <{ [inj@b<ω> v] }> ω /\
    Σ ⊢ τ ≡ ω1 ~+ ω2.
Proof.
  type_inv_solver by hauto lq: on solve: equiv_naive_solver
                           ctrs: oval inv: oval.
Qed.

Lemma type_inv_case Σ Γ l e0 e1 e2 τ :
  Σ; Γ ⊢ case{l} e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' κ L1 L2,
    Σ; Γ ⊢ τ' :: κ /\
    Σ; Γ ⊢ e0 : τ1 +{l} τ2 /\
    (forall x, x ∉ L1 -> Σ; (<[x:=τ1]> Γ) ⊢ e1^x : τ') /\
    (forall x, x ∉ L2 -> Σ; (<[x:=τ2]> Γ) ⊢ e2^x : τ') /\
    Σ ⊢ τ ≡ τ'.
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

Lemma type_inv_ite Σ Γ l e0 e1 e2 τ :
  Σ; Γ ⊢ if{l} e0 then e1 else e2 : τ ->
  exists τ',
    Σ; Γ ⊢ e0 : 𝔹{l} /\
    Σ; Γ ⊢ e1 : τ' /\
    Σ; Γ ⊢ e2 : τ' /\
    Σ ⊢ τ ≡ τ'.
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
  | _; _ ⊢ inj{_}@_<_> _ : _ => tac type_inv_inj
  | _; _ ⊢ ~if _ then _ else _ : _ => tac type_inv_mux
  | _; _ ⊢ if _ then _ else _ : _ => tac type_inv_ite
  | _; _ ⊢ ~case _ of _ | _ : _ => tac type_inv_ocase
  | _; _ ⊢ case{_} _ of _ | _ : _ => tac type_inv_case
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

(** ** Properties of [otval] and [oval] *)

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

Lemma oval_elim v ω :
  oval v ω ->
  val v /\ otval ω /\ ∅; ∅ ⊢ v : ω.
Proof.
  intros H. use H.
  induction H; hauto lq:on ctrs: val, otval, typing.
Qed.

Lemma oval_intro v ω Σ Γ :
  val v ->
  otval ω ->
  Σ; Γ ⊢ v : ω ->
  oval v ω.
Proof.
  intros H. revert ω.
  induction H; inversion 1; intros; subst;
    apply_type_inv;
    simpl_whnf_equiv;
    try hauto lq: on rew: off
              ctrs: oval, typing
              use: otval_well_kinded
              solve: equiv_naive_solver.

  (* Case [inj@_<_> _] *)
  repeat match goal with
         | H : _ ⊢ ?ω1 ≡ ?ω2 |- _ =>
           apply otval_uniq in H; try qauto l: on inv: otval
         end.
Qed.

(** We can always find an inhabitant for any oblivious type value. *)
Lemma oval_inhabited ω :
  otval ω ->
  exists v, oval v ω.
Proof.
  induction 1; try qauto ctrs: oval.
  (* Case [~+]: we choose left injection as inhabitant. *)
  sfirstorder use: (OVOSum true).
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

End M.
