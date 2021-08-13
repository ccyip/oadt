(** Lemmas about parallel reduction and equivalence. *)
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.

Import syntax.notations.
Import semantics.notations.
Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

Section equivalence.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

Notation "e '==>!' e'" := (Σ ⊢ e ==>! e')
                            (at level 40,
                             e' constr at level 0).

(** * Lemmas about parallel reduction *)

(** ** Properties of oblivious values *)

Lemma pared_oval v e :
  oval v ->
  v ==>! e ->
  v = e.
Proof.
  intros H. revert e.
  induction H; intros ?; inversion 1; intros; subst; eauto; hauto.
Qed.

Lemma pared_otval ω τ :
  otval ω ->
  ω ==>! τ ->
  ω = τ.
Proof.
  intros H. revert τ.
  induction H; intros ?; inversion 1; intros; subst; eauto; hauto.
Qed.


(** ** Substitution lemmas *)

(* Technically [lc e1] should imply [lc e1'], but I have this assumption for
convenience. *)
Lemma pared_subst1_ e s s' x :
  lc s -> lc s' ->
  lc e ->
  s ==>! s' ->
  <{ {x↦s}e }> ==>! <{ {x↦s'}e }>.
Proof.
  intros ??.
  induction 1; intros; simpl; try case_decide; eauto using pared;
    econstructor; eauto using lc;
      simpl_cofin?;
      rewrite <- !subst_open_comm by (eauto; fast_set_solver!!); eauto.
Qed.

(** From now on, well-formedness of [Σ] is needed. *)
#[local]
Set Default Proof Using "Hwf".

Lemma pared_subst1 e s s' x :
  s ==>! s' ->
  lc e ->
  <{ {x↦s}e }> ==>! <{ {x↦s'}e }>.
Proof.
  intros. eapply pared_subst1_; qauto use: pared_lc.
Qed.

Lemma pared_subst_ e e' s s' x :
  lc s -> lc s' ->
  e ==>! e' ->
  s ==>! s' ->
  <{ {x↦s}e }> ==>! <{ {x↦s'}e' }>.
Proof.
  intros ??.
  induction 1; intros; simpl; eauto using pared_subst1;
    (* Massage the goal so the induction hypotheses can be applied. *)
    rewrite ?subst_ite_distr;
    rewrite ?subst_open_distr by assumption;
    repeat match goal with
           | H : oval ?v |- _ =>
             rewrite !(subst_fresh v) by shelve
           | H : otval ?ω |- _ =>
             rewrite !(subst_fresh ω) by shelve
           end;
    econstructor; simpl_cofin?;
      (* Apply induction hypotheses first before solving other side
      conditions. *)
      lazymatch goal with
      | |- _ ==>! _ =>
        rewrite <- ?subst_open_comm by (eauto; shelve);
          auto_apply
      | _ => idtac
      end; eauto;
        repeat lazymatch goal with
               | |- _ !! _ = Some _ =>
                 rewrite subst_fresh by shelve; eauto
               | |- ovalty _ _ =>
                 rewrite subst_fresh by shelve; eauto
               | |- lc _ =>
                 eauto using subst_lc
               end; eauto.

  Unshelve.

  all : try fast_set_solver!!; simpl_fv; fast_set_solver*!!.
Qed.

Lemma pared_subst e e' s s' x :
  e ==>! e' ->
  s ==>! s' ->
  <{ {x↦s}e }> ==>! <{ {x↦s'}e' }>.
Proof.
  qauto use: pared_subst_, pared_lc.
Qed.

Lemma pared_open e e' s s' x :
  <{ e^x }> ==>! <{ e'^x }> ->
  s ==>! s' ->
  x ∉ fv e ∪ fv e' ->
  <{ e^s }> ==>! <{ e'^s'}>.
Proof.
  intros.
  rewrite (subst_intro e _ x) by fast_set_solver!!.
  rewrite (subst_intro e' _ x) by fast_set_solver!!.
  eapply pared_subst; eauto.
Qed.

Lemma pared_open1 e s s' :
  s ==>! s' ->
  lc <{ e^s }> ->
  <{ e^s }> ==>! <{ e^s'}>.
Proof.
  intros.
  destruct (exist_fresh (fv e)) as [x ?].
  unshelve eapply pared_open; eauto.
  constructor. eauto using lc, open_respect_lc, pared_lc1.
  fast_set_solver!!.
Qed.

Lemma pared_rename e e' x y :
  <{ e^x }> ==>! <{ e'^x }> ->
  x ∉ fv e ∪ fv e' ->
  <{ e^y }> ==>! <{ e'^y }>.
Proof.
  intros.
  eapply pared_open; eauto using lc.
  econstructor; eauto using lc.
Qed.

(** ** Admissible introduction rules *)

Ltac intro_solver :=
  intros; econstructor; eauto; simpl_cofin;
    eapply pared_rename; eauto; try fast_set_solver!!.

Lemma ROCase_intro b ω1 ω2 v v1 v2 e1 e2 e1' e2' x :
  <{ e1^x }> ==>! <{ e1'^x }> ->
  <{ e2^x }> ==>! <{ e2'^x }> ->
  oval v ->
  ovalty v1 ω1 -> ovalty v2 ω2 ->
  x ∉ fv e1 ∪ fv e1' ∪ fv e2 ∪ fv e2' ->
  <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> ==>!
    <{ ~if [b] then (ite b (e1'^v) (e1'^v1)) else (ite b (e2'^v2) (e2'^v)) }>.
Proof.
  intro_solver.
Qed.

Lemma RApp_intro τ e1 e2 e1' e2' x :
  e1 ==>! e1' ->
  <{ e2^x }> ==>! <{ e2'^x }> ->
  lc τ ->
  x ∉ fv e2 ∪ fv e2' ->
  <{ (\:τ => e2) e1 }> ==>! <{ e2'^e1' }>.
Proof.
  intro_solver.
Qed.

Lemma RLet_intro e1 e2 e1' e2' x :
  e1 ==>! e1' ->
  <{ e2^x }> ==>! <{ e2'^x }> ->
  x ∉ fv e2 ∪ fv e2' ->
  <{ let e1 in e2 }> ==>! <{ e2'^e1' }>.
Proof.
  intro_solver.
Qed.

Lemma RCase_intro b τ e0 e1 e2 e0' e1' e2' x:
  e0 ==>! e0' ->
  <{ e1^x }> ==>! <{ e1'^x }> ->
  <{ e2^x }> ==>! <{ e2'^x }> ->
  lc τ ->
  x ∉ fv e1 ∪ fv e1' ∪ fv e2 ∪ fv e2' ->
  <{ case inj@b<τ> e0 of e1 | e2 }> ==>! <{ ite b (e1'^e0') (e2'^e0') }>.
Proof.
  intro_solver.
Qed.

Lemma RCongPi_intro τ1 τ2 τ1' τ2' x :
  τ1 ==>! τ1' ->
  <{ τ2^x }> ==>! <{ τ2'^x }> ->
  x ∉ fv τ2 ∪ fv τ2' ->
  <{ Π:τ1, τ2 }> ==>! <{ Π:τ1', τ2' }>.
Proof.
  intro_solver.
Qed.

Lemma RCongAbs_intro τ e τ' e' x :
  τ ==>! τ' ->
  <{ e^x }> ==>! <{ e'^x }> ->
  x ∉ fv e ∪ fv e' ->
  <{ \:τ => e }> ==>! <{ \:τ' => e' }>.
Proof.
  intro_solver.
Qed.

Lemma RCongCase_intro l e0 e1 e2 e0' e1' e2' x :
  e0 ==>! e0' ->
  <{ e1^x }> ==>! <{ e1'^x }> ->
  <{ e2^x }> ==>! <{ e2'^x }> ->
  x ∉ fv e1 ∪ fv e1' ∪ fv e2 ∪ fv e2' ->
  <{ case{l} e0 of e1 | e2 }> ==>! <{ case{l} e0' of e1' | e2' }>.
Proof.
  intro_solver.
Qed.

(** ** Inversion lemmas *)

Ltac inv_solver :=
  inversion 1; subst; try apply_lc_inv; repeat esplit; eauto using pared.

Lemma pared_inv_abs τ e t :
  <{ \:τ => e }> ==>! t ->
  exists τ' e' L,
    t = <{ \:τ' => e' }> /\
    τ ==>! τ' /\
    (forall x, x ∉ L -> <{ e^x }> ==>! <{ e'^x }>).
Proof.
  inv_solver.
Qed.

Lemma pared_inv_pair e1 e2 t :
  <{ (e1, e2) }> ==>! t ->
  exists e1' e2',
    t = <{ (e1', e2') }> /\
    e1 ==>! e1' /\
    e2 ==>! e2'.
Proof.
  inv_solver.
Qed.

Lemma pared_inv_fold X e t :
  <{ fold<X> e }> ==>! t ->
  exists e',
    t = <{ fold<X> e' }> /\
    e ==>! e'.
Proof.
  inv_solver.
Qed.

Lemma pared_inv_inj b τ e t :
  <{ inj@b<τ> e }> ==>! t ->
  exists τ' e',
    t = <{ inj@b<τ'> e' }> /\
    τ ==>! τ' /\
    e ==>! e'.
Proof.
  inv_solver.
Qed.

End equivalence.

Ltac pared_intro_ e :=
  match e with
  | <{ (\:_ => _) _ }> => eapply RApp_intro
  | <{ ~case [inj@_<_> _] of _ | _ }> => eapply ROCase_intro
  | <{ let _ in _ }> => eapply RLet_intro
  | <{ case inj@_<_> _ of _ | _ }> => eapply RCase_intro
  | <{ Π:_, _ }> => eapply RCongPi_intro
  | <{ \:_ => _ }> => eapply RCongAbs_intro
  | <{ case{_} _ of _ | _ }> => eapply RCongCase_intro
  | _ => econstructor
  end.

Ltac pared_intro :=
  match goal with
  | |- _ ⊢ ?e ==>! _ => pared_intro_ e
  end.

Ltac apply_pared_inv_ e H :=
  match e with
  | <{ \:_ => _ }> => apply pared_inv_abs in H; try simp_hyp H
  | <{ (_, _) }> => apply pared_inv_pair in H; try simp_hyp H
  | <{ fold<_> _ }> => apply pared_inv_fold in H; try simp_hyp H
  | <{ inj@_<_> _ }> => apply pared_inv_inj in H; try simp_hyp H
  | _ => head_constructor e; sinvert H
  end.

Ltac apply_pared_inv :=
  match goal with
  | H : _ ⊢ ?e ==>! _ |- _ => apply_pared_inv_ e H
  end; subst; eauto.

Tactic Notation "lcrefl" "by" tactic3(tac) := eapply RRefl; tac.
Tactic Notation "lcrefl" := lcrefl by eauto using lc.

(** ** Confluence theorem *)

Section equivalence.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

Notation "e '==>!' e'" := (Σ ⊢ e ==>! e')
                            (at level 40,
                             e' constr at level 0).
Notation "e '==>*' e'" := (Σ ⊢ e ==>* e')
                            (at level 40,
                             e' custom oadt at level 99).
Notation "e ≡ e'" := (Σ ⊢ e ≡ e').

(** The diamond property. *)
Lemma pared_diamond e e1 e2 :
  e ==>! e1 ->
  e ==>! e2 ->
  exists e',
    e1 ==>! e' /\
    e2 ==>! e'.
Proof.
  intros H. revert e2.
  induction H; intros;
    repeat apply_pared_inv;
    try apply_gctx_wf; simplify_map_eq;
      (* Massage hypotheses related to oblivious values. *)
      try select! (oval _)
          (fun H => dup_hyp H (fun H => apply oval_lc in H));
      try select! (otval _)
          (fun H => dup_hyp H (fun H => apply otval_lc in H));
      try select! (ovalty _ _)
          (fun H => dup_hyp H (fun H => apply ovalty_lc in H; destruct H));
      repeat
        match goal with
        | H : oval ?v, H' : ?v ==>! _ |- _ =>
          eapply pared_oval in H'; [| solve [ eauto ] ]
        | H : otval ?ω, H' : ?ω ==>! _ |- _ =>
          eapply pared_otval in H'; [| solve [ eauto ]]
        end; subst;
        (* Solve some easy cases. *)
        try solve [ repeat esplit; eauto;
                    econstructor; eauto using lc ];
        (* Generate local closure assumptions to avoid reproving the same
        stuff. *)
        repeat apply_lc_inv;
        simpl_cofin?;
          (* Generate more local closure assumptions. *)
          try select! (_ ==>! _)
              (fun H => match type of H with
                      | _ ==>! ?e =>
                        try assert (lc e) by eauto using pared_lc2
                      end);
          (* Mung the induction hypotheses. *)
          repeat
            match goal with
            | H : context [exists _, ?u ==>! _ /\ _] |- _ =>
              let e := fresh "e" in
              let H1 := fresh "H" in
              let H2 := fresh "H" in
              edestruct H as [e [H1 H2]]; [
                (* Discharge assumptions in the induction hypotheses. *)
                try match goal with
                    | |- ?e ==>! _ => head_constructor e; pared_intro
                    end;
                (* Be careful to not generate the useless induction
                hypotheses. *)
                try match goal with
                    | H : ?e ==>! ?e' |- ?e ==>! _ =>
                      lazymatch u with
                      | context [e'] => fail
                      | _ => apply H
                      end
                    end; solve [ eauto ]
               |];
              clear H;
              try assert (lc e) by eauto using pared_lc2;
              let go H :=
                  lazymatch type of H with
                  | ?e' ==>! _ =>
                    (* Massage the parallel reduction assumptions to the right
                    form. *)
                    try lazymatch e' with
                        | <{ ?e'^(fvar ?x) }> =>
                          rewrite <- (open_close e x) in H by assumption
                        end
                  end
              in go H1; go H2
            end;
    (* May invert some generated induction hypotheses. *)
    repeat apply_pared_inv;
    (* Solve more easy cases. *)
    try solve [ try case_split; repeat esplit; eauto;
                econstructor; eauto using lc ];
    (* Solve the trickier cases. *)
    let go _ :=
        lazymatch goal with
        | |- ?e ==>! ?e' =>
          eauto;
            match e with
            | <{ _^?e2 }> =>
              eapply pared_open; [ assumption
                                 | solve [eauto] || lcrefl
                                 | solve [eauto] || lcrefl
                                 | .. ]
            | _ => head_constructor e; pared_intro
            | _ => lcrefl
            end
        end;
          lazymatch goal with
          | |- _ ∉ _ => shelve
          | |- lc _ =>
            eauto using lc, typing_lc, kinding_lc
          | |- _ => eauto
          end
    in try solve [ repeat esplit; go ()
                 | case_split; repeat esplit; do 2 go ()
                 (* Sometimes I have to solve the right hand side first. *)
                 | repeat esplit; cycle 1;
                   solve [ do 2 go ()
                         | case_split; do 2 go () ] ].

  (* Application of abstraction. *)
  match goal with
  | H : context [exists _, <{ \:_ => ?e }> ==>! _ /\ _] |- _ =>
    (* Avoid generating useless hypothesis. *)
    match goal with
    | H : _ ==>! ?e' |- _ =>
      lazymatch e' with
      | context [e] => clear H
      end
    end;
      edestruct H as [? [??]]; [
        pared_intro; eauto; set_shelve
       |]
  end.
  repeat apply_pared_inv.
  simpl_cofin.
  repeat esplit; [ pared_intro | eapply pared_open ];
    eauto; set_shelve.

  Unshelve.
  all : eauto; rewrite ?close_fv by eauto; fast_set_solver!!.
Qed.

Lemma pared_confluence_ e e1 e2 :
  e ==>* e1 ->
  e ==>! e2 ->
  exists e',
    e1 ==>! e' /\
    e2 ==>* e'.
Proof.
  intros H. revert e2.
  induction H; intros.
  - match goal with
      | H : _ ==>! _, H' : _ ==>! _ |- _ =>
        edestruct pared_diamond as [? [??]];
          [ apply H | apply H' | .. ]
      end.
    hauto use: rt_step.
  - hauto use: rt_step.
  - repeat match goal with
           | H : forall e', ?e ==>! e' -> _, H' : ?e ==>! _ |- _ =>
               edestruct H as [? [??]]; eauto; clear H
           end.
    hauto use: rt_trans.
Qed.

Lemma pared_confluence e e1 e2 :
  e ==>* e1 ->
  e ==>* e2 ->
  exists e',
    e1 ==>* e' /\
    e2 ==>* e'.
Proof.
  intros H. revert e2.
  induction H; intros.
  - edestruct pared_confluence_ as [? [??]]; eauto.
    hauto use: rt_step.
  - hauto use: rt_step.
  - repeat match goal with
           | H : forall e', ?e ==>* e' -> _, H' : ?e ==>* _ |- _ =>
               edestruct H as [? [??]]; eauto; clear H
           end.
    hauto use: rt_trans.
Qed.

(** * Lemmas about expression equivalence *)

Lemma pared_equiv_iff_join e1 e2 :
  e1 ≡ e2 <-> pared_equiv_join Σ e1 e2.
Proof.
  split.
  - induction 1;
      hauto ctrs: pared_equiv_join, clos_refl_trans, pared inv: pared_equiv_join.
  - intros [].
    (* Another equivalent definition of the closure is easier in this case. *)
    repeat match goal with
           | H : _ ==>* _ |- _ =>
             apply clos_rt_rt1n in H
           end.

    select (clos_refl_trans_1n _ _ _ _) (fun H => induction H);
        try hauto ctrs: pared_equiv.
    select (clos_refl_trans_1n _ _ _ _) (fun H => induction H);
      hauto ctrs: pared_equiv.
Qed.

(** [pared_equiv] is an equivalence *)

#[global]
Instance pared_equiv_is_refl : Reflexive (pared_equiv Σ).
Proof.
  hnf; intros; econstructor.
Qed.

#[global]
Instance pared_equiv_is_symm : Symmetric (pared_equiv Σ).
Proof.
  hnf; intros; srewrite pared_equiv_iff_join;
    hauto ctrs: pared_equiv_join inv: pared_equiv_join.
Qed.

#[global]
Instance pared_equiv_is_trans : Transitive (pared_equiv Σ).
Proof.
  hnf. intros ??? H1 H2.
  srewrite pared_equiv_iff_join.
  destruct H1 as [e1 e e1'].
  destruct H2 as [e e2 e2'].
  edestruct (pared_confluence e e1' e2') as [? [??]]; eauto.
  econstructor; eapply rt_trans; eauto.
Qed.

(* Is there a conventional way to achieve this? *)
Hint Extern 0 (gctx_wf _) => eassumption : typeclass_instances.

(** ** Weak head normal form *)
(** I only use weak head normal form as a machinery for proofs right now, so
only the necessary cases (for types) are defined. But I may extend it with other
expressions later. *)
Inductive whnf : expr -> Prop :=
| WUnitT : whnf <{ 𝟙 }>
| WBool{l} : whnf <{ 𝔹{l} }>
| WPi τ1 τ2 : whnf <{ Π:τ1, τ2 }>
| WProd τ1 τ2 : whnf <{ τ1 * τ2 }>
| WSum l τ1 τ2 : whnf <{ τ1 +{l} τ2 }>
| WADT X τ :
    Σ !! X = Some (DADT τ) ->
    whnf <{ gvar X }>
.

(** Type equivalence for the weak head normal form fragments. This relation
always assumes that the two arguments are already in [whnf]. *)
Inductive whnf_equiv : expr -> expr -> Prop :=
| WQUnitT : whnf_equiv <{ 𝟙 }> <{ 𝟙 }>
| WQBool l : whnf_equiv <{ 𝔹{l} }> <{ 𝔹{l} }>
| WQPi τ1 τ2 τ1' τ2' L :
    τ1 ≡ τ1' ->
    (forall x, x ∉ L -> <{ τ2^x }> ≡ <{ τ2'^x }>) ->
    whnf_equiv <{ Π:τ1, τ2 }> <{ Π:τ1', τ2' }>
| WQProd τ1 τ2 τ1' τ2' :
    τ1 ≡ τ1' ->
    τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 * τ2 }> <{ τ1' * τ2' }>
| WQSum l τ1 τ2 τ1' τ2' :
    τ1 ≡ τ1' ->
    τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 +{l} τ2 }> <{ τ1' +{l} τ2' }>
| WQADT X : whnf_equiv <{ gvar X }> <{ gvar X }>
.

#[global]
Instance whnf_equiv_is_symm : Symmetric whnf_equiv.
Proof.
  hnf. induction 1; econstructor; simpl_cofin?; equiv_naive_solver.
Qed.

Lemma pared_whnf τ1 τ2 :
  τ1 ==>! τ2 ->
  whnf τ1 ->
  whnf τ2.
Proof.
  induction 1; eauto; intros Hw;
    try lazymatch type of Hw with
        | whnf ?e =>
          head_constructor e; sinvert Hw
        end;
    simplify_map_eq; try solve [econstructor].
Qed.

Lemma pared_whnf_equiv τ1 τ1' τ2 :
  τ1 ==>! τ1' ->
  whnf τ1 ->
  whnf_equiv τ1' τ2 ->
  whnf_equiv τ1 τ2.
Proof.
  intros H. revert τ2.
  induction H; eauto; intros ? Hw;
    try lazymatch type of Hw with
        | whnf ?e =>
          head_constructor e; sinvert Hw
        end; intros;
    simplify_map_eq;
  select (whnf_equiv _ _) (fun H => sinvert H);
  econstructor; simpl_cofin?;
  eauto using pared_equiv.
Qed.

(** [whnf_equiv] refines [pared_equiv] under some side conditions. *)
Lemma pared_equiv_whnf_equiv τ1 τ2 :
  τ1 ≡ τ2 ->
  whnf τ1 -> whnf τ2 ->
  whnf_equiv τ1 τ2.
Proof.
  induction 1.
  - intros [] []; econstructor; simpl_cofin?; equiv_naive_solver.
  - hauto use: pared_whnf, pared_whnf_equiv.
  - intros.
    symmetry.
    match goal with
    | H : context [whnf_equiv _ _] |- _ => symmetry in H
    end.
    hauto use: pared_whnf, pared_whnf_equiv.
Qed.

Lemma otval_whnf ω :
  otval ω ->
  whnf ω.
Proof.
  induction 1; sfirstorder.
Qed.

(** ** Relation to operational semantics *)

(** [pared] refines [step]. *)
Lemma pared_step e e' :
  Σ ⊨ e -->! e' ->
  lc e ->
  e ==>! e'.
Proof.
  induction 1; intros; try select (ectx _) (fun H => sinvert H);
    repeat apply_lc_inv;
    repeat econstructor; eauto.
Qed.

Lemma pared_equiv_pared e e' :
  e ==>! e' ->
  e ≡ e'.
Proof.
  eauto using pared_equiv.
Qed.

(** expressions always step to equivalent expressions. *)
Lemma pared_equiv_step e e' :
  Σ ⊨ e -->! e' ->
  lc e ->
  e ≡ e'.
Proof.
  hauto use: pared_step, pared_equiv_pared.
Qed.

#[local]
Set Default Proof Using "Hwf".

(** ** Substitution lemmas *)
Lemma pared_equiv_subst1 e s s' x :
  s ≡ s' ->
  lc e ->
  {x↦s}e ≡ {x↦s'}e.
Proof.
  intros H ?.
  induction H;
    econstructor; solve [ eauto using pared_subst1 ].
Qed.

Lemma pared_equiv_subst2 e e' s x :
  e ≡ e' ->
  lc s ->
  {x↦s}e ≡ {x↦s}e'.
Proof.
  intros H ?.
  induction H; intros;
    hauto ctrs: pared_equiv, pared using pared_subst.
Qed.

(** Different combinations of local closure conditions are possible. *)
Lemma pared_equiv_subst e e' s s' x :
  e ≡ e' ->
  s ≡ s' ->
  lc e ->
  lc s' ->
  {x↦s}e ≡ {x↦s'}e'.
Proof.
  intros.
  etrans.
  eapply pared_equiv_subst1; eauto.
  eapply pared_equiv_subst2; eauto.
Qed.

Lemma pared_equiv_rename τ τ' x y :
  τ ≡ τ' ->
  {x↦y}τ ≡ {x↦y}τ'.
Proof.
  eauto using lc, pared_equiv_subst2.
Qed.

(** A few alternative statements exist, e.g., having [x] as an argument. But this
one is the most convenient. *)
Lemma pared_equiv_open1 e s s' L :
  s ≡ s' ->
  (forall x, x ∉ L -> lc <{ e^x }>) ->
  <{ e^s }> ≡ <{ e^s' }>.
Proof.
  intros.
  simpl_cofin.
  rewrite (subst_intro e s _) by fast_set_solver!!.
  rewrite (subst_intro e s' _) by fast_set_solver!!.
  eauto using pared_equiv_subst1.
Qed.

Lemma pared_equiv_open2 e e' s x :
  <{ e^x }> ≡ <{ e'^x }> ->
  lc s ->
  x ∉ fv e ∪ fv e' ->
  <{ e^s }> ≡ <{ e'^s }>.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  rewrite (subst_intro e' s x) by fast_set_solver!!.
  eauto using pared_equiv_subst2.
Qed.

Lemma pared_equiv_open e e' s s' x :
  <{ e^x }> ≡ <{ e'^x }> ->
  s ≡ s' ->
  lc <{ e^x }> ->
  lc s' ->
  x ∉ fv e ∪ fv e' ->
  <{ e^s }> ≡ <{ e'^s' }>.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  rewrite (subst_intro e' s' x) by fast_set_solver!!.
  eauto using pared_equiv_subst.
Qed.

(** ** Congruence lemmas *)

(* Another proof strategy is to reduce them to [pared_equiv_subst]. *)

Ltac congr_solver :=
  intros H1 H2; intros;
    induction H1;
    solve [ hauto ctrs: pared_equiv, pared use: pared_lc
          | induction H2; hauto ctrs: pared_equiv, pared use: pared_lc ].

Lemma pared_equiv_congr_prod τ1 τ1' τ2 τ2' :
  τ1 ≡ τ1' ->
  τ2 ≡ τ2' ->
  lc τ1 ->
  lc τ2 ->
  lc τ2' ->
  <{ τ1 * τ2 }> ≡ <{ τ1' * τ2' }>.
Proof.
  congr_solver.
Qed.

Lemma pared_equiv_congr_sum τ1 τ1' τ2 τ2' l :
  τ1 ≡ τ1' ->
  τ2 ≡ τ2' ->
  lc τ1 ->
  lc τ2 ->
  lc τ2' ->
  <{ τ1 +{l} τ2 }> ≡ <{ τ1' +{l} τ2' }>.
Proof.
  congr_solver.
Qed.

Lemma pared_equiv_congr_inj τ τ' e e' l b :
  τ ≡ τ' ->
  e ≡ e' ->
  lc τ ->
  lc e ->
  lc e' ->
  <{ inj{l}@b<τ> e }> ≡ <{ inj{l}@b<τ'> e' }>.
Proof.
  congr_solver.
Qed.

(** This is good enough for our purposes though it is weaker than it could be. *)
Lemma pared_equiv_congr_pi τ1 τ1' τ2 x :
  τ1 ≡ τ1' ->
  lc <{ τ2^x }> ->
  <{ Π:τ1, τ2 }> ≡ <{ Π:τ1', τ2 }>.
Proof.
  intros H; intros.
  induction H;
    econstructor;
    solve [ eauto; econstructor; eauto;
            simpl_cofin?; lcrefl by eauto using lc_rename ].
Qed.

End equivalence.

Hint Extern 0 (gctx_wf _) => eassumption : typeclass_instances.

(** * Tactics *)

(** Simplify type equivalence to [whnf_equiv]. Possibly derive contradiction if
two equivalent types in [whnf] have different head. *)
Tactic Notation "simpl_whnf_equiv" "by" tactic3(tac) :=
  match goal with
  | H : _ ⊢ ?τ1 ≡ ?τ2 |- _ =>
    apply pared_equiv_whnf_equiv in H;
    [ sinvert H
    | solve [tac]
    | solve [tac] ]
  end.

Tactic Notation "simpl_whnf_equiv" :=
  simpl_whnf_equiv by eauto using whnf, otval_whnf.

Ltac apply_pared_equiv_congr :=
  lazymatch goal with
  | |- _ ⊢ Π:_, _ ≡ Π: _, _ => eapply pared_equiv_congr_pi
  | |- _ ⊢ _ * _ ≡ _ * _ => eapply pared_equiv_congr_prod
  | |- _ ⊢ _ +{_} _ ≡ _ +{_} _ => eapply pared_equiv_congr_sum
  | |- _ ⊢ inj{_}@_<_> _ ≡ inj{_}@_<_> _ => eapply pared_equiv_congr_inj
  end.
