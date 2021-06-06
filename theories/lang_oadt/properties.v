From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.

(** * Properties *)
(** Lemmas for various definitions. *)

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

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

(** ** Properities of [actx] *)
Lemma actx_map_insert e1 e2 Φ f :
  actx_map f (set_insert (e1, e2) Φ) ≡ set_insert (f e1, f e2) (actx_map f Φ).
Proof.
  unfold actx_map.
  rewrite set_map_insert.
  reflexivity.
Qed.

Lemma actx_map_in e1 e2 Φ f :
  (e1, e2) ∈ Φ ->
  (f e1, f e2) ∈ (actx_map f Φ).
Proof.
  unfold actx_map.
  intros. eapply elem_of_map_2_alt; eauto.
Qed.

(** ** Weak head normal form *)
(** I only use weak head normal form as a machinery for proofs right now, so
only the necessary cases (for types) are defined. But I may extend it with other
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
Inductive whnf_equiv {Σ : gctx} {Φ : actx} : expr -> expr -> Prop :=
| WQUnitT : whnf_equiv <{ 𝟙 }> <{ 𝟙 }>
| WQBool l : whnf_equiv <{ 𝔹{l} }> <{ 𝔹{l} }>
| WQPi τ1 τ2 τ1' τ2' L :
    Σ; Φ ⊢ τ1 ≡ τ1' ->
    (forall x, x ∉ L -> Σ; Φ ⊢ τ2^x ≡ τ2'^x) ->
    whnf_equiv <{ Π:τ1, τ2 }> <{ Π:τ1', τ2' }>
| WQProd τ1 τ2 τ1' τ2' :
    Σ; Φ ⊢ τ1 ≡ τ1' ->
    Σ; Φ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 * τ2 }> <{ τ1' * τ2' }>
| WQSum l τ1 τ2 τ1' τ2' :
    Σ; Φ ⊢ τ1 ≡ τ1' ->
    Σ; Φ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 +{l} τ2 }> <{ τ1' +{l} τ2' }>
| WQADT X : whnf_equiv <{ gvar X }> <{ gvar X }>
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

Instance expr_equiv_is_equiv Σ Φ : Equivalence (expr_equiv Σ Φ).
Proof.
  split; hnf; qauto ctrs: expr_equiv.
Qed.

Lemma expr_equiv_actx_equiv Σ Φ1 Φ2 τ1 τ2 :
  Σ; Φ1 ⊢ τ1 ≡ τ2 ->
  Φ1 ≡ Φ2 ->
  Σ; Φ2 ⊢ τ1 ≡ τ2.
Proof.
  induction 1; intros; eauto with expr_equiv; try equiv_naive_solver.
  apply QAsm. set_solver.
Qed.

Lemma expr_equiv_actx_id Σ Φ e1 e2 :
  Σ; ({{e1 ≡ e2}}Φ) ⊢ e1 ≡ e2.
Proof.
  apply QAsm.
  set_solver.
Qed.

Lemma expr_equiv_actx_cut Σ Φ e1 e2 τ1 τ2 :
  Σ; ({{e1 ≡ e2}}Φ) ⊢ τ1 ≡ τ2 ->
  Σ; Φ ⊢ e1 ≡ e2 ->
  Σ; Φ ⊢ τ1 ≡ τ2.
Proof.
  remember ({{e1 ≡ e2}}Φ) as Φ'.
  induction 1; intros; subst; eauto with expr_equiv; try equiv_naive_solver.
  select (_ ∈ _) (fun H => set_unfold; destruct H);
    simp_hyps; eauto with expr_equiv.
Qed.

Lemma expr_equiv_weakening Σ Φ τ τ' :
  Σ; Φ ⊢ τ ≡ τ' ->
  forall Σ' Φ',
    Σ ⊆ Σ' ->
    Φ ⊆ Φ' ->
    Σ'; Φ' ⊢ τ ≡ τ'.
Proof.
  induction 1; intros; eauto using lookup_weaken with expr_equiv;
    try equiv_naive_solver.
Qed.

Lemma expr_equiv_subst1 Σ Φ τ τ' x s :
  gctx_wf Σ ->
  lc s ->
  Σ; Φ ⊢ τ ≡ τ' ->
  Σ; (actx_map ({x↦s}) Φ) ⊢ {x↦s}τ ≡ {x↦s}τ'.
Proof.
  intros Hwf Hlc.
  induction 1; intros; simpl;
    rewrite ?subst_ite_distr;
    rewrite ?subst_open_distr by eauto;
    eauto with expr_equiv; try equiv_naive_solver.

  (* [QAppOADT] and [QFun] *)
  1-2: econstructor; rewrite subst_fresh; eauto;
    select (Σ !! _ = _) (fun H => apply Hwf in H; simp_hyp H);
    simpl_cofin?; simpl_fv; fast_set_solver*!!.

  (* [QOCase] and [QOInj] *)
  1-2: match goal with
       | H : oval ?v |- _ =>
         rewrite ?(subst_fresh v); rewrite ?(subst_fresh ω)
       end; [ econstructor | .. ]; eauto;
    simpl_fv; fast_set_solver!!.

  (* Cases with binders *)
  1-4:
  econstructor; eauto;
  simpl_cofin;
  rewrite <- !subst_open_comm by (eauto; fast_set_solver!!); eauto.

  (* [QAsm] *)
  apply QAsm.
  eauto using actx_map_in.
Qed.

Lemma expr_equiv_subst2 Σ Φ τ x e e' :
  lc e ->
  lc e' ->
  lc τ ->
  Σ; Φ ⊢ e ≡ e' ->
  Σ; Φ ⊢ {x↦e}τ ≡ {x↦e'}τ.
Proof.
  intros Hlc1 Hlc2.
  induction 1; intros; simpl; try case_decide; eauto with expr_equiv.

  all: econstructor; eauto;
    simpl_cofin;
    rewrite <- !subst_open_comm by (eauto; fast_set_solver!!); eauto.
Qed.

Instance expr_equiv_actx_iff_proper :
  Proper ((=) ==> (≡) ==> (=) ==> (=) ==> iff) expr_equiv.
Proof.
  solve_proper_prepare.
  split; intros; eapply expr_equiv_actx_equiv; equiv_naive_solver.
Qed.

Lemma expr_equiv_rename Σ Φ τ τ' x y :
  gctx_wf Σ ->
  Σ; Φ ⊢ τ ≡ τ' ->
  Σ; (actx_map ({x↦y}) Φ) ⊢ {x↦y}τ ≡ {x↦y}τ'.
Proof.
  eauto using expr_equiv_subst1 with lc.
Qed.

Lemma expr_equiv_open1 Σ Φ τ1 τ2 x e :
  gctx_wf Σ ->
  lc e ->
  Σ; Φ ⊢ τ1^x ≡ τ2^x ->
  x ∉ fv τ1 ∪ fv τ2 ∪ actx_fv Φ ->
  Σ; Φ ⊢ τ1^e ≡ τ2^e.
Proof.
  intros.
  erewrite (subst_intro τ1 e x) by fast_set_solver!!.
  erewrite (subst_intro τ2 e x) by fast_set_solver!!.
  erewrite <- (subst_actx_fresh Φ x e) by fast_set_solver!!.
  eapply expr_equiv_subst1; eauto.
Qed.

Lemma expr_equiv_open2 Σ Φ τ e1 e2 :
  lc e1 ->
  lc e2 ->
  (exists L, forall x, x ∉ L -> lc <{ τ^x }>) ->
  Σ; Φ ⊢ e1 ≡ e2 ->
  Σ; Φ ⊢ τ^e1 ≡ τ^e2.
Proof.
  intros.
  simp_hyps.
  simpl_cofin.
  erewrite (subst_intro τ e1 x) by eassumption.
  erewrite (subst_intro τ e2 x) by eassumption.
  eauto using expr_equiv_subst2.
Qed.

Lemma expr_equiv_weakening_actx_insert Σ Φ e1 e2 τ1 τ2 :
  Σ; Φ ⊢ τ1 ≡ τ2 ->
  Σ; ({{e1 ≡ e2}}Φ) ⊢ τ1 ≡ τ2.
Proof.
  intros. eapply expr_equiv_weakening; eauto.
  fast_set_solver!!.
Qed.

Lemma expr_equiv_step Σ Φ e e' :
  Σ ⊨ e -->! e' ->
  Σ; Φ ⊢ e ≡ e'.
Proof.
  induction 1; try select (ectx _) (fun H => sinvert H);
    eauto with expr_equiv.

  (* Oblivious case *)
  etrans; [ econstructor; eauto | ].
  symmetry.
  etrans; [ econstructor; eauto | ].
  hauto.

  (* Generated by the cofinite quantifiers. *)
  Unshelve.
  all : exact ∅.
Qed.

Instance pared_is_refl Σ Φ : Reflexive (pared Σ Φ).
Proof.
  hnf; econstructor.
Qed.

Inductive asm_wf : asm -> Prop :=
| AWIte x b :
    asm_wf (<{ fvar x }>, <{ lit b }>)
| AWCase x y τ b :
    lc τ ->
    asm_wf (<{ fvar x }>, <{ inj@b<τ> y }>)
.
Hint Constructors asm_wf : asm_wf.

Definition actx_wf : actx -> Prop := set_Forall asm_wf.

Ltac apply_actx_wf :=
  match goal with
  | H : actx_wf ?Φ, H' : (_, _) ∈ ?Φ |- _ =>
    apply H in H'; sinvert H'
  end.

Lemma actx_wf_lc Φ e1 e2 :
  actx_wf Φ ->
  (e1, e2) ∈ Φ ->
  lc e1 /\ lc e2.
Proof.
  intros.
  apply_actx_wf; hauto l: on ctrs: lc.
Qed.

Lemma pared_inv_abs Σ Φ τ e1 e2 :
  actx_wf Φ ->
  Σ; Φ ⊢ \:τ => e1 ==>! e2 ->
  exists τ' e1',
    e2 = <{ \:τ' => e1' }> /\
    Σ; Φ ⊢ τ ==>! τ' /\
    (exists L, forall x, x ∉ L -> Σ; Φ ⊢ e1^x ==>! e1'^x).
Proof.
  intros Hwf.
  inversion 1; subst; try apply_actx_wf; repeat esplit; eauto with pared.

  Unshelve.
  all : exact ∅.
Qed.

Ltac apply_pared_inv :=
  match goal with
  | H : _; _ ⊢ \:_ => _ ==>! _ |- _ => apply pared_inv_abs in H; try simp_hyp H
  end; subst; eauto.

(* TODO: move *)
Ltac apply_lc_inv :=
  match goal with
  | H : lc ?e |- _ => head_constructor e; sinvert H
  end.

(* TODO: also use it in other cases *)
Ltac apply_gctx_wf :=
  match goal with
  | Hwf : gctx_wf ?Σ, H : ?Σ !! _ = _ |- _ => apply Hwf in H; try simp_hyp H
  end.

Lemma pared_lc Σ Φ e e' :
  gctx_wf Σ ->
  actx_wf Φ ->
  Σ; Φ ⊢ e ==>! e' ->
  lc e ->
  lc e'.
Proof.
  intros Hwf ?.
  induction 1; intros; eauto with lc;
    repeat apply_lc_inv;
    try apply_gctx_wf;
    try solve [ econstructor; simpl_cofin?; eauto
              | simpl_cofin?; eauto using lc_open_atom_lc, typing_lc, kinding_lc
              | simpl_cofin?; qauto use: lc_open_atom_lc ctrs: lc ].

  qauto use: actx_wf_lc.
Qed.

(* Technically [lc e1] should imply [lc e1']. *)
Lemma pared_subst1 Σ Φ e e1 e1' x :
  lc e1 -> lc e1' ->
  lc e ->
  Σ; Φ ⊢ e1 ==>! e1' ->
  Σ; Φ ⊢ {x↦e1}e ==>! {x↦e1'}e.
Proof.
  intros ??.
  induction 1; intros; simpl; try case_decide; eauto with pared;
    econstructor; eauto;
      simpl_cofin?;
      rewrite <- !subst_open_comm by (eauto; fast_set_solver!!); eauto.
Qed.

Ltac relax_pared :=
  match goal with
  | |- ?Σ; ?Φ ⊢ ?e ==>! ?e' =>
    refine (eq_ind _ (fun e' => Σ; Φ ⊢ e ==>! e') _ _ _)
  end.

Lemma pared_subst Σ Φ e1 e1' e2 e2' x :
  lc e1 -> lc e1' -> lc e2 ->
  gctx_wf Σ ->
  Σ; Φ ⊢ e2 ==>! e2' ->
  Σ; Φ ⊢ e1 ==>! e1' ->
  Σ; Φ ⊢ {x↦e1}e2 ==>! {x↦e1'}e2'.
Proof.
  intros ????.
  induction 1; intros; simpl; eauto using pared_subst1.
  all:
    repeat apply_lc_inv.
  all:
    rewrite ?subst_ite_distr;
    rewrite ?subst_open_distr by assumption;
    repeat match goal with
           | H : oval ?v |- _ =>
             rewrite !(subst_fresh v) by shelve
           | H : otval ?ω |- _ =>
             rewrite !(subst_fresh ω) by shelve
           end.
  1-12:
    econstructor; simpl_cofin?;
    lazymatch goal with
    | |- _; _ ⊢ _ ==>! _ =>
      rewrite <- ?subst_open_comm by (eauto; shelve);
        auto_apply
    | _ => idtac
    end; eauto;
    repeat lazymatch goal with
           | |- _ !! _ = Some _ =>
             rewrite subst_fresh by shelve; eauto
           end; eauto.

  1-14:
    econstructor; simpl_cofin?;
    lazymatch goal with
    | |- _; _ ⊢ _ ==>! _ =>
      rewrite <- ?subst_open_comm by (eauto; shelve);
        auto_apply
    | _ => idtac
    end; eauto;
    repeat lazymatch goal with
           | |- _ !! _ = Some _ =>
             rewrite subst_fresh by shelve; eauto
           end; eauto.

    relax_pared.
    econstructor.
    Focus 3.
    match goal with
    | H : otval ?v |- _ =>
      rewrite ?(subst_fresh v)
    end.
    reflexivity.
    simpl_fv.
    fast_set_solver!!.
    rewrite ?(subst_fresh ω); eauto.
    simpl_fv.
    fast_set_solver!!.


Lemma pared_open Σ Φ e1 e1' e2 e2' x :
  Σ; Φ ⊢ e2 ==>! e2' ->
  Σ; Φ ⊢ e1^x ==>! e1'^x ->
  x ∉ fv e1 ∪ fv e1' ->
  Σ; Φ ⊢ e1^e2 ==>! e1'^e2'.
Proof.
  intros.
  rewrite (subst_intro e1 _ x) by fast_set_solver!!.
  rewrite (subst_intro e1' _ x) by fast_set_solver!!.
  eauto using pared_subst.
Admitted.

Lemma pared_diamond Σ Φ e e1 e2 :
  actx_wf Φ ->
  Σ; Φ ⊢ e ==>! e1 ->
  Σ; Φ ⊢ e ==>! e2 ->
  exists e',
    Σ; Φ ⊢ e1 ==>! e' /\
    Σ; Φ ⊢ e2 ==>! e'.
Proof.
  intros Hwf H. revert e2.
  induction H; intros.
  (* - qauto ctrs: pared. *)
  (* - sinvert H. *)
  (*   + repeat esplit; econstructor. *)
  (*   + repeat esplit; econstructor. *)
  (*   + apply_pared_inv. *)
  (*     repeat esplit. 2 : apply RApp. *)
Admitted.


Lemma pared_confluence Σ Φ e e1 e2 :
  Σ; Φ ⊢ e ==>* e1 ->
  Σ; Φ ⊢ e ==>* e2 ->
  exists e',
    Σ; Φ ⊢ e1 ==>* e' /\
    Σ; Φ ⊢ e2 ==>* e'.
Proof.
Admitted.

(* FIXME *)
Lemma pared_equiv_iff_alt Σ Φ e1 e2 :
  Σ; Φ ⊢ e1 ≡ᵣ e2 <-> Σ; Φ ⊢ e1 ≡ⱼ e2.
Proof.
  split.
  - induction 1; try hauto ctrs: pared_equiv_alt, clos_refl_trans_1n inv: pared_equiv_alt.
  - induction 1.
    induction H.
    induction H0.
    econstructor.
    econstructor; solve [eauto].
    econstructor; solve [eauto].
Qed.

(* FIXME *)
Instance pared_equiv_alt_is_equiv Σ Φ : Equivalence (pared_equiv_alt Σ Φ).
Proof.
  split; hnf; intros.
  - repeat econstructor.
  - induction H; econstructor; solve [eauto].
  - induction H; induction H0.
    eapply pared_confluence in H1; eauto.
    simp_hyps.
    econstructor;
    eapply Operators_Properties.clos_rt_rt1n;
    eapply rt_trans;
    eapply Operators_Properties.clos_rt1n_rt; eauto.
Qed.

Instance pared_equiv_is_equiv Σ Φ : Equivalence (pared_equiv Σ Φ).
Proof.
  split; hnf; intros; srewrite pared_equiv_iff_alt; equiv_naive_solver.
Qed.

Lemma expr_equiv_pared Σ Φ e1 e2 :
  Σ; Φ ⊢ e1 ==>! e2 ->
  Σ; Φ ⊢ e1 ≡ e2.
Proof.
  induction 1; simpl_cofin?; eauto with expr_equiv.
Admitted.

Lemma expr_equiv_iff_pared_equiv Σ Φ e1 e2 :
  Σ; Φ ⊢ e1 ≡ᵣ e2 <-> Σ; Φ ⊢ e1 ≡ e2.
Proof.
  split.
  - induction 1;
      try select (_; _ ⊢ _ ==>! _) (fun H => apply expr_equiv_pared in H);
      equiv_naive_solver.
Admitted.

(* Lemma pared_obliv_type_preserve Σ Γ τ τ' : *)
(*   gctx_wf Σ -> *)
(*   Σ; ∅ ⊢ τ ==>! τ' -> *)
(*   Σ; ∅; Γ ⊢ τ :: *@O -> *)
(*   Σ; ∅; Γ ⊢ τ' :: *@O. *)
(* Proof. *)
(*   intros H. revert Γ. *)
(*   induction H; intros; eauto; apply_kind_inv*; simplify_eq. *)
(*   (* simpl_cofin. *) *)
(*   (* apply H1 in H6. *) *)
(*   Admitted. *)

(* Lemma expr_equiv_obliv_type_preserve Σ Γ τ τ' κ : *)
(*   gctx_wf Σ -> *)
(*   Σ; ∅ ⊢ τ ≡ τ' -> *)
(*   Σ; ∅; Γ ⊢ τ :: *@O -> *)
(*   Σ; ∅; Γ ⊢ τ' :: κ -> *)
(*      whnf Σ τ' -> *)
(*   Σ; ∅; Γ ⊢ τ' :: *@O. *)
(* Proof. *)
(*   intros Hwf. *)
(*   rewrite <- expr_equiv_iff_pared_equiv. *)
(*   induction 1; intros; eauto. *)
(*   - auto_apply; eauto. *)
(*     shelve. *)
(*   - *)
(* Admitted. *)

Instance whnf_equiv_is_symm Σ Φ : Symmetric (whnf_equiv Σ Φ).
Proof.
  hnf. induction 1; econstructor; simpl_cofin?; equiv_naive_solver.
Qed.

Lemma pared_whnf Σ τ1 τ2 :
  Σ; ∅ ⊢ τ1 ==>! τ2 ->
  whnf Σ τ1 ->
  whnf Σ τ2.
Proof.
  induction 1; eauto; intros Hw;
    try lazymatch type of Hw with
        | whnf _ ?e =>
          head_constructor e; sinvert Hw
        end;
    simplify_map_eq; try solve [econstructor];
      set_solver.
Qed.

(* FIXME *)
Lemma pared_whnf_equiv Σ τ1 τ1' τ2 :
  Σ; ∅ ⊢ τ1 ==>! τ1' ->
  whnf Σ τ1 ->
  whnf_equiv Σ ∅ τ1' τ2 ->
  whnf_equiv Σ ∅ τ1 τ2.
Proof.
  intros H. revert τ2.
  induction H; eauto; intros ? Hw;
    try lazymatch type of Hw with
        | whnf _ ?e =>
          head_constructor e; sinvert Hw
        end; intros;
    simplify_map_eq.

  sinvert H1.
  econstructor;
  rewrite <- expr_equiv_iff_pared_equiv in *; econstructor; eauto.
  sinvert H1.
  econstructor;
  rewrite <- expr_equiv_iff_pared_equiv in *; econstructor; eauto.
  sinvert H2.
  econstructor; simpl_cofin?;
  rewrite <- expr_equiv_iff_pared_equiv in *; econstructor; eauto.
  set_solver.
  set_solver.
Qed.

(** [whnf_equiv] refines [expr_equiv] under some side conditions. Note that this
lemma assumes [actx] is empty for convenience, but it is not necessary. We would
need to reason about the consistency of [actx] though if we want to relax it. *)
(* FIXME *)
Lemma expr_equiv_whnf_equiv Σ τ1 τ2 :
  Σ; ∅ ⊢ τ1 ≡ τ2 ->
  whnf Σ τ1 -> whnf Σ τ2 ->
  whnf_equiv Σ ∅ τ1 τ2.
Proof.
  rewrite <- expr_equiv_iff_pared_equiv.
  induction 1.
  - destruct 1; destruct 1; simplify_eq; econstructor; simpl_cofin?;
    try equiv_naive_solver.
  - intros. feed specialize IHpared_equiv; eauto using pared_whnf.
    eauto using pared_whnf_equiv.
  - intros. feed specialize IHpared_equiv; eauto using pared_whnf.
    symmetry in IHpared_equiv.
    symmetry.
    eauto using pared_whnf_equiv.
Qed.

(** Simplify type equivalence to [whnf_equiv]. Possibly derive contradiction if
two equivalent types in [whnf] have different head. *)
Tactic Notation "simpl_whnf_equiv" "by" tactic3(tac) :=
  match goal with
  | H : _; _ ⊢ ?τ1 ≡ ?τ2 |- _ =>
    apply expr_equiv_whnf_equiv in H;
    [ sinvert H
    | solve [tac]
    | solve [tac] ]
  end.

Tactic Notation "simpl_whnf_equiv" :=
  simpl_whnf_equiv by eauto using otval_whnf with whnf.

(** ** Equivariant Lemmas *)

Lemma typing_kinding_actx_equiv Σ :
  (forall Φ1 Γ e τ,
      Σ; Φ1; Γ ⊢ e : τ ->
      forall Φ2,
        Φ1 ≡ Φ2 ->
        Σ; Φ2; Γ ⊢ e : τ) /\
  (forall Φ1 Γ τ κ,
      Σ; Φ1; Γ ⊢ τ :: κ ->
      forall Φ2,
        Φ1 ≡ Φ2 ->
        Σ; Φ2; Γ ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind; intros;
    try hauto l:on rew:off ctrs: typing, kinding.

  (* [TIf] and [TCase] *)
  1-2: econstructor; eauto; simpl_cofin?; auto_apply; fast_set_solver*!!.

  (* [TConv] *)
  econstructor; eauto.
  select (_ ≡ _) (fun H => rewrite <- H). auto.
Qed.

Instance typing_actx_iff_proper :
  Proper ((=) ==> (≡) ==> (=) ==> (=) ==> (=) ==> iff) typing.
Proof.
  unfold Proper, respectful.
  qauto use: typing_kinding_actx_equiv.
Qed.

Instance kinding_actx_iff_proper :
  Proper ((=) ==> (≡) ==> (=) ==> (=) ==> (=) ==> iff) kinding.
Proof.
  unfold Proper, respectful.
  qauto use: typing_kinding_actx_equiv.
Qed.

(** ** Cut Lemma *)
(** NOTE: this is one of the most crucial lemmas for preservation *)
Lemma typing_kinding_actx_cut_ Σ e1 e2 :
  (forall Φ' Γ e τ,
      Σ; Φ'; Γ ⊢ e : τ ->
      forall Φ,
        Φ' ≡ {{e1 ≡ e2}}Φ ->
        Σ; Φ ⊢ e1 ≡ e2 ->
        Σ; Φ; Γ ⊢ e : τ) /\
  (forall Φ' Γ τ κ,
      Σ; Φ'; Γ ⊢ τ :: κ ->
      forall Φ,
        Φ' ≡ {{e1 ≡ e2}}Φ ->
        Σ; Φ ⊢ e1 ≡ e2 ->
        Σ; Φ; Γ ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind; intros; subst;
    try hauto l: on ctrs: typing, kinding.

  (* [TIf] and [TCase] *)
  1-2: econstructor; eauto; simpl_cofin?; auto_apply;
    eauto using expr_equiv_weakening_actx_insert;
    fast_set_solver*!!.

  (* [TConv] *)
  qauto ctrs: typing use: expr_equiv_actx_cut, expr_equiv_actx_equiv.
Qed.

Lemma typing_actx_cut Σ Φ Γ e e1 e2 τ :
  Σ; ({{e1 ≡ e2}}Φ); Γ ⊢ e : τ ->
  Σ; Φ ⊢ e1 ≡ e2 ->
  Σ; Φ; Γ ⊢ e : τ.
Proof.
  intros.
  eapply typing_kinding_actx_cut_; eauto.
Qed.

Lemma typing_actx_cut_refl Σ Φ Γ e e' τ :
  Σ; ({{e' ≡ e'}}Φ); Γ ⊢ e : τ ->
  Σ; Φ; Γ ⊢ e : τ.
Proof.
  intros.
  eapply typing_actx_cut; eauto.
  reflexivity.
Qed.

(** * Inversion Lemmas *)

(** ** Kind inversion  *)
Tactic Notation "kind_inv_solver" "by" tactic3(tac) :=
  match goal with
  | |- _; _; _ ⊢ ?τ :: _ -> _ => remember τ
  end;
  induction 1; subst; simp_hyps; simplify_eq;
  tac.

Tactic Notation "kind_inv_solver" :=
  kind_inv_solver by (repeat esplit; eauto; lattice_naive_solver).

Lemma kind_inv_pi Σ Φ Γ τ1 τ2 κ :
  Σ; Φ; Γ ⊢ Π:τ1, τ2 :: κ ->
  κ = <{ *@M }> /\
  exists L κ1 κ2,
    (∀ x, x ∉ L → Σ; Φ; (<[x:=τ1]> Γ) ⊢ τ2^x :: κ2) /\
    Σ; Φ; Γ ⊢ τ1 :: κ1.
Proof.
  kind_inv_solver by sfirstorder use: top_inv.
Qed.

Lemma kind_inv_bool Σ Φ Γ κ :
  Σ; Φ; Γ ⊢ 𝔹 :: κ -> <{ *@P }> ⊑ κ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_prod Σ Φ Γ τ1 τ2 κ :
  Σ; Φ; Γ ⊢ τ1 * τ2 :: κ ->
  exists κ',
    Σ; Φ; Γ ⊢ τ1 :: κ' /\
    Σ; Φ; Γ ⊢ τ2 :: κ' /\
    <{ κ' }> ⊑ κ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sum Σ Φ Γ τ1 τ2 κ :
  Σ; Φ; Γ ⊢ τ1 + τ2 :: κ ->
  <{ *@P }> ⊑ κ /\
  exists κ',
    Σ; Φ; Γ ⊢ τ1 :: κ' /\
    Σ; Φ; Γ ⊢ τ2 :: κ'.
Proof.
  kind_inv_solver by qauto l: on solve: lattice_naive_solver
                           use: join_ub_r.
Qed.

Lemma kind_inv_osum Σ Φ Γ τ1 τ2 κ :
  Σ; Φ; Γ ⊢ τ1 ~+ τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  Σ; Φ; Γ ⊢ τ1 :: *@O /\
  Σ; Φ; Γ ⊢ τ2 :: *@O.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_gvar Σ Φ Γ X κ :
  Σ; Φ; Γ ⊢ gvar X :: κ ->
  <{ *@P }> ⊑ κ /\ exists τ, Σ !! X = Some (DADT τ).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_app Σ Φ Γ e1 e2 κ :
  Σ; Φ; Γ ⊢ e1 e2 :: κ ->
  <{ *@O }> ⊑ κ /\
  exists X τ e',
    Σ !! X = Some (DOADT τ e') /\
    Σ; Φ; Γ ⊢ e2 : τ /\
    e1 = <{ gvar X }>.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ite Σ Φ Γ l e0 τ1 τ2 κ :
  Σ; Φ; Γ ⊢ if{l} e0 then τ1 else τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  l = low /\
  Σ; Φ; Γ ⊢ e0 : 𝔹 /\
  Σ; Φ; Γ ⊢ τ1 :: *@O /\
  Σ; Φ; Γ ⊢ τ2 :: *@O.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_let Σ Φ Γ e τ κ :
  Σ; Φ; Γ ⊢ let e in τ :: κ ->
  <{ *@O }> ⊑ κ /\
  exists τ' L,
    Σ; Φ; Γ ⊢ e : τ' /\
    (forall x, x ∉ L -> Σ; Φ; (<[x:=τ']> Γ) ⊢ τ^x :: *@O).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_case Σ Φ Γ l e0 τ1 τ2 κ :
  Σ; Φ; Γ ⊢ case{l} e0 of τ1 | τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  l = low /\
  exists τ1' τ2' L1 L2,
    Σ; Φ; Γ ⊢ e0 : τ1' + τ2' /\
    (forall x, x ∉ L1 -> Σ; Φ; (<[x:=τ1']> Γ) ⊢ τ1^x :: *@O) /\
    (forall x, x ∉ L2 -> Σ; Φ; (<[x:=τ2']> Γ) ⊢ τ2^x :: *@O).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_mux Σ Φ Γ e0 e1 e2 κ :
  Σ; Φ; Γ ⊢ ~if e0 then e1 else e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sec Σ Φ Γ e κ :
  Σ; Φ; Γ ⊢ s𝔹 e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_pair Σ Φ Γ e1 e2 κ :
  Σ; Φ; Γ ⊢ (e1, e2) :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_proj Σ Φ Γ b e κ :
  Σ; Φ; Γ ⊢ π@b e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_inj Σ Φ Γ l b τ e κ :
  Σ; Φ; Γ ⊢ inj{l}@b<τ> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ocase Σ Φ Γ e0 e1 e2 κ :
  Σ; Φ; Γ ⊢ ~case e0 of e1 | e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_fold Σ Φ Γ X e κ :
  Σ; Φ; Γ ⊢ fold<X> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_unfold Σ Φ Γ X e κ :
  Σ; Φ; Γ ⊢ unfold<X> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_abs Σ Φ Γ τ e κ :
  Σ; Φ; Γ ⊢ \:τ => e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Tactic Notation "apply_kind_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _; _ ⊢ Π:_, _ :: _ => tac kind_inv_pi
  | _; _; _ ⊢ 𝔹 :: _ => tac kind_inv_bool
  | _; _; _ ⊢ _ _ :: _ => tac kind_inv_app
  | _; _; _ ⊢ let _ in _ :: _ => tac kind_inv_let
  | _; _; _ ⊢ _ * _ :: _ => tac kind_inv_prod
  | _; _; _ ⊢ _ + _ :: _ => tac kind_inv_sum
  | _; _; _ ⊢ _ ~+ _ :: _ => tac kind_inv_osum
  | _; _; _ ⊢ gvar _ :: _ => tac kind_inv_gvar
  | _; _; _ ⊢ ~if _ then _ else _ :: _ => apply kind_inv_mux in H; elim H
  | _; _; _ ⊢ if{_} _ then _ else _ :: _ => tac kind_inv_ite
  | _; _; _ ⊢ ~case _ of _ | _ :: _ => apply kind_inv_ocase in H; elim H
  | _; _; _ ⊢ case{_} _ of _ | _ :: _ => tac kind_inv_case
  | _; _; _ ⊢ s𝔹 _ :: _ => apply kind_inv_sec in H; elim H
  | _; _; _ ⊢ (_, _) :: _ => apply kind_inv_pair in H; elim H
  | _; _; _ ⊢ π@_ _ :: _ => apply kind_inv_proj in H; elim H
  | _; _; _ ⊢ inj{_}@_<_> _ :: _ => apply kind_inv_inj in H; elim H
  | _; _; _ ⊢ fold<_> _ :: _ => apply kind_inv_fold in H; elim H
  | _; _; _ ⊢ unfold<_> _ :: _ => apply kind_inv_unfold in H; elim H
  | _; _; _ ⊢ \:_ => _ :: _ => apply kind_inv_abs in H; elim H
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
  | |- _; _; _ ⊢ ?e : _ -> _ => remember e
  end;
  induction 1; subst; simp_hyps; simplify_eq;
  tac.

Tactic Notation "type_inv_solver" :=
  type_inv_solver by (repeat esplit; eauto; equiv_naive_solver).

Lemma type_inv_unit Σ Φ Γ τ :
  Σ; Φ; Γ ⊢ () : τ ->
  Σ; Φ ⊢ τ ≡ 𝟙.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_lit Σ Φ Γ b τ :
  Σ; Φ; Γ ⊢ lit b : τ ->
  Σ; Φ ⊢ τ ≡ 𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_abs Σ Φ Γ e τ2 τ :
  Σ; Φ; Γ ⊢ \:τ2 => e : τ ->
  exists τ1 κ L,
    Σ; Φ; Γ ⊢ τ2 :: κ /\
    (forall x, x ∉ L -> Σ; Φ; (<[x:=τ2]> Γ) ⊢ e^x : τ1^x) /\
    Σ; Φ ⊢ τ ≡ Π:τ2, τ1.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_gvar Σ Φ Γ x τ :
  Σ; Φ; Γ ⊢ gvar x : τ ->
  exists τ' e,
    Σ !! x = Some (DFun τ' e) /\
    Σ; Φ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_pair Σ Φ Γ e1 e2 τ :
  Σ; Φ; Γ ⊢ (e1, e2) : τ ->
  exists τ1 τ2,
    Σ; Φ; Γ ⊢ e1 : τ1 /\
    Σ; Φ; Γ ⊢ e2 : τ2 /\
    Σ; Φ ⊢ τ ≡ τ1 * τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_inj Σ Φ Γ l b e τ' τ :
  Σ; Φ; Γ ⊢ inj{l}@b<τ'> e : τ ->
  exists τ1 τ2,
    τ' = <{ τ1 +{l} τ2 }> /\
    Σ; Φ; Γ ⊢ τ1 +{l} τ2 :: ite l *@O *@P /\
    Σ; Φ; Γ ⊢ e : ite b τ1 τ2 /\
    Σ; Φ ⊢ τ ≡ τ1 +{l} τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_fold Σ Φ Γ X e τ :
  Σ; Φ; Γ ⊢ fold<X> e : τ ->
  exists τ',
    Σ; Φ; Γ ⊢ e : τ' /\
    Σ !! X = Some (DADT τ') /\
    Σ; Φ ⊢ τ ≡ gvar X.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_boxedlit Σ Φ Γ b τ :
  Σ; Φ; Γ ⊢ [b] : τ ->
  Σ; Φ ⊢ τ ≡ ~𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_boxedinj Σ Φ Γ b v ω τ :
  Σ; Φ; Γ ⊢ [inj@b<ω> v] : τ ->
  exists ω1 ω2,
    ω = <{ ω1 ~+ ω2 }> /\
    ovalty <{ [inj@b<ω> v] }> ω /\
    Σ; Φ ⊢ τ ≡ ω1 ~+ ω2.
Proof.
  type_inv_solver by hauto lq: on solve: equiv_naive_solver
                           ctrs: ovalty inv: ovalty.
Qed.

Lemma type_inv_case Σ Φ Γ e0 e1 e2 τ :
  Σ; Φ; Γ ⊢ case e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' κ L1 L2,
    Σ; Φ; Γ ⊢ τ' :: κ /\
    Σ; Φ; Γ ⊢ e0 : τ1 + τ2 /\
    (forall x, x ∉ L1 -> Σ; ({{e0 ≡ inl<(τ1 + τ2)> x}} Φ); (<[x:=τ1]> Γ) ⊢ e1^x : τ') /\
    (forall x, x ∉ L2 -> Σ; ({{e0 ≡ inr<(τ1 + τ2)> x}} Φ); (<[x:=τ2]> Γ) ⊢ e2^x : τ') /\
    Σ; Φ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_ocase Σ Φ Γ e0 e1 e2 τ :
  Σ; Φ; Γ ⊢ ~case e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' L1 L2,
    Σ; Φ; Γ ⊢ τ' :: *@O /\
    Σ; Φ; Γ ⊢ e0 : τ1 ~+ τ2 /\
    (forall x, x ∉ L1 -> Σ; Φ; (<[x:=τ1]> Γ) ⊢ e1^x : τ') /\
    (forall x, x ∉ L2 -> Σ; Φ; (<[x:=τ2]> Γ) ⊢ e2^x : τ') /\
    Σ; Φ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_case_ Σ Φ Γ l e0 e1 e2 τ :
  Σ; Φ; Γ ⊢ case{l} e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' κ L1 L2,
    Σ; Φ; Γ ⊢ τ' :: κ /\
    Σ; Φ; Γ ⊢ e0 : τ1 +{l} τ2 /\
    (forall x, x ∉ L1 -> exists Φ', Σ; Φ'; (<[x:=τ1]> Γ) ⊢ e1^x : τ') /\
    (forall x, x ∉ L2 -> exists Φ', Σ; Φ'; (<[x:=τ2]> Γ) ⊢ e2^x : τ') /\
    Σ; Φ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver by (repeat (esplit; eauto); equiv_naive_solver).
Qed.

Lemma type_inv_prod Σ Φ Γ τ1 τ2 τ :
  Σ; Φ; Γ ⊢ τ1 * τ2 : τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_sum Σ Φ Γ l τ1 τ2 τ :
  Σ; Φ; Γ ⊢ τ1 +{l} τ2 : τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_app Σ Φ Γ e1 e2 τ :
  Σ; Φ; Γ ⊢ e1 e2 : τ ->
  exists τ1 τ2,
    Σ; Φ; Γ ⊢ e1 : Π:τ2, τ1 /\
    Σ; Φ; Γ ⊢ e2 : τ2 /\
    Σ; Φ ⊢ τ ≡ τ1^e2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_let Σ Φ Γ e1 e2 τ :
  Σ; Φ; Γ ⊢ let e1 in e2 : τ ->
  exists τ1 τ2 L,
    Σ; Φ; Γ ⊢ e1 : τ1 /\
    (forall x, x ∉ L -> Σ; Φ; (<[x:=τ1]> Γ) ⊢ e2^x : τ2^x) /\
    Σ; Φ ⊢ τ ≡ τ2^e1.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_sec Σ Φ Γ e τ :
  Σ; Φ; Γ ⊢ s𝔹 e : τ ->
  Σ; Φ; Γ ⊢ e : 𝔹 /\
  Σ; Φ ⊢ τ ≡ ~𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_ite Σ Φ Γ e0 e1 e2 τ :
  Σ; Φ; Γ ⊢ if e0 then e1 else e2 : τ ->
  exists τ' κ,
    Σ; Φ; Γ ⊢ e0 : 𝔹 /\
    Σ; ({{e0 ≡ lit true}} Φ); Γ ⊢ e1 : τ' /\
    Σ; ({{e0 ≡ lit false}} Φ); Γ ⊢ e2 : τ' /\
    Σ; Φ; Γ ⊢ τ' :: κ /\
    Σ; Φ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_mux Σ Φ Γ e0 e1 e2 τ :
  Σ; Φ; Γ ⊢ ~if e0 then e1 else e2 : τ ->
  exists τ',
    Σ; Φ; Γ ⊢ e0 : ~𝔹 /\
    Σ; Φ; Γ ⊢ e1 : τ' /\
    Σ; Φ; Γ ⊢ e2 : τ' /\
    Σ; Φ; Γ ⊢ τ' :: *@O /\
    Σ; Φ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_proj Σ Φ Γ b e τ :
  Σ; Φ; Γ ⊢ π@b e : τ ->
  exists τ1 τ2,
    Σ; Φ; Γ ⊢ e : τ1 * τ2 /\
    Σ; Φ ⊢ τ ≡ ite b τ1 τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_unfold Σ Φ Γ X e τ :
  Σ; Φ; Γ ⊢ unfold<X> e : τ ->
  exists τ',
    Σ !! X = Some (DADT τ') /\
    Σ; Φ; Γ ⊢ e : gvar X /\
    Σ; Φ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Tactic Notation "apply_type_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _; _ ⊢ () : _ => tac type_inv_unit
  | _; _; _ ⊢ lit _ : _ => tac type_inv_lit
  | _; _; _ ⊢ gvar _ : _ => tac type_inv_gvar
  | _; _; _ ⊢ \:_ => _ : _ => tac type_inv_abs
  | _; _; _ ⊢ _ _ : _ => tac type_inv_app
  | _; _; _ ⊢ let _ in _ : _ => tac type_inv_let
  | _; _; _ ⊢ (_, _) : _ => tac type_inv_pair
  | _; _; _ ⊢ s𝔹 _ : _ => tac type_inv_sec
  | _; _; _ ⊢ π@_ _ : _ => tac type_inv_proj
  | _; _; _ ⊢ inj{_}@_<_> _ : _ => tac type_inv_inj
  | _; _; _ ⊢ ~if _ then _ else _ : _ => tac type_inv_mux
  | _; _; _ ⊢ if _ then _ else _ : _ => tac type_inv_ite
  | _; _; _ ⊢ ~case _ of _ | _ : _ => tac type_inv_ocase
  | _; _; _ ⊢ case _ of _ | _ : _ => tac type_inv_case
  | _; _; _ ⊢ case{_} _ of _ | _ : _ => tac type_inv_case_
  | _; _; _ ⊢ fold<_> _ : _ => tac type_inv_fold
  | _; _; _ ⊢ unfold<_> _ : _ => tac type_inv_unfold
  | _; _; _ ⊢ [_] : _ => tac type_inv_boxedlit
  | _; _; _ ⊢ [inj@_<_> _] : _ => tac type_inv_boxedinj
  | _; _; _ ⊢ _ * _ : _ => apply type_inv_prod in H; elim H
  | _; _; _ ⊢ _ +{_} _ : _ => apply type_inv_sum in H; elim H
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

Lemma typing_expr_wf Σ Φ Γ e τ :
  Σ; Φ; Γ ⊢ e : τ ->
  expr_wf e
with kinding_expr_wf Σ Φ Γ τ κ :
  Σ; Φ; Γ ⊢ τ :: κ ->
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

Lemma otval_well_kinded ω Σ Φ Γ :
  otval ω ->
  Σ; Φ; Γ ⊢ ω :: *@O.
Proof.
  induction 1; hauto lq: on ctrs: kinding solve: lattice_naive_solver.
Qed.

Lemma otval_uniq Σ Φ ω1 ω2 :
  otval ω1 ->
  otval ω2 ->
  Σ; Φ ⊢ ω1 ≡ ω2 ->
  ω1 = ω2.
Proof.
  intros H. revert ω2.
  induction H; intros; simpl_whnf_equiv;
    qauto l:on rew:off inv: otval.
Qed.

Lemma ovalty_elim v ω:
  ovalty v ω ->
  oval v /\ otval ω /\ forall Σ Φ Γ, Σ; Φ; Γ ⊢ v : ω.
Proof.
  induction 1; hauto lq: on ctrs: oval, ovalty, otval, typing.
Qed.

Lemma ovalty_elim_alt v ω:
  ovalty v ω ->
  val v /\ otval ω /\ forall Σ Φ Γ, Σ; Φ; Γ ⊢ v : ω.
Proof.
  hauto use: ovalty_elim, oval_val.
Qed.

Lemma ovalty_intro_alt v ω Σ Φ Γ :
  val v ->
  otval ω ->
  Σ; Φ; Γ ⊢ v : ω ->
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
         | H : _; _ ⊢ ?ω1 ≡ ?ω2 |- _ =>
           apply otval_uniq in H; try qauto l: on use: ovalty_elim inv: otval
         end.
Qed.

Lemma ovalty_intro v ω Σ Φ Γ :
  oval v ->
  otval ω ->
  Σ; Φ; Γ ⊢ v : ω ->
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

Lemma any_kind_otval Σ Φ Γ τ :
  Σ; Φ; Γ ⊢ τ :: *@A ->
  otval τ.
Proof.
  remember <{ *@A }>.
  induction 1; subst; try hauto ctrs: otval.
  - srewrite join_bot_iff. easy.
  - eauto using bot_inv.
Qed.

(** ** Tactics *)

Ltac case_ite_expr :=
  lazymatch goal with
  | |- _; _; _ ⊢ ?e : _ =>
    lazymatch e with
    | context [<{ ite ?b _ _ }>] => destruct b
    end
  | |- _; _; _ ⊢ ?τ :: _ =>
    lazymatch τ with
    | context [<{ ite ?b _ _ }>] => destruct b
    end
  end.

Ltac case_label :=
  lazymatch goal with
  | |- context [<{ inj{?l}@_<_> _ }>] => destruct l
  | |- context [<{ if{?l} _ then _ else _ }>] => destruct l
  | |- context [<{ case{?l} _ of _ | _ }>] => destruct l
  | |- context [<{ 𝔹{?l} }>] => destruct l
  | |- context [<{ _ +{?l} _ }>] => destruct l
  end.
