From oadt Require Import idt.
From oadt.lang_oadt Require Import
     base syntax semantics typing infrastructure
     equivalence values head preservation.
Import syntax.notations typing.notations.

Ltac tsf_pared ctor R :=
  let H := fresh in
  pose proof ctor as H;
  repeat
    lazymatch type of H with
    | ?T -> ?T' =>
        lazymatch T with
        | lc _ => specialize_any H
        | _ =>
            match eval pattern pared in T with
            | ?P _ =>
                let P := eval simpl in (P (fun Σ => rtc (pared Σ))) in
                refine (P -> _ : Prop); specialize_any H
            end
        end
    | forall e : ?T, _ =>
        refine (forall e : T, _ : Prop); specialize (H e)
    | ?Σ ⊢ ?e ⇛ ?e' => exact (R Σ e e')
    end.

MetaCoq Run (tsf_ind_gen_from
               pared "mpared"
               ltac:(tsf_ctors pared (append "M") tsf_pared)).

Section fix_gctx.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).

#[local]
Set Default Proof Using "All".

Lemma mpared_lc e e' :
  lc e ->
  e ⇛* e' ->
  lc e'.
Proof.
  eapply rtc_preserve; eauto using pared_lc2.
Qed.

Lemma mpared_preservation Γ e l e' τ :
  Γ ⊢ e :{l} τ ->
  e ⇛* e' ->
  Γ ⊢ e' :{l} τ.
Proof.
  eapply rtc_preserve with (P := fun e => Γ ⊢ e :{l} τ).
  eauto using pared_preservation.
Qed.

Lemma mpared_woval ω τ :
  woval ω ->
  ω ⇛* τ ->
  woval τ.
Proof.
  eapply rtc_preserve; eauto using pared_woval.
Qed.

Lemma mpared_body e e' L :
  body e ->
  (forall x, x ∉ L -> <{ e^x }> ⇛* <{ e'^x }>) ->
  body e'.
Proof.
  unfold body.
  intros. simp_hyps. eexists. simpl_cofin. eauto using mpared_lc.
Qed.

Lemma mpared_subst1 e s s' x :
  s ⇛* s' ->
  lc e ->
  <{ {x↦s}e }> ⇛* <{ {x↦s'}e }>.
Proof.
  induction 1; try reflexivity.
  econstructor; eauto using pared_subst1.
Qed.

(** Similar to [mpared_subst1], but for the cases when the substitution is a
[body]. The whole proof strategy for [mpared_sound] using this lemma is not
particularly elegant. *)
Lemma mpared_subst_body1 e s s' x L :
  (* This condition may be provable with some side conditions, but it is too
  much work. *)
  (forall s s' L,
      (forall x, x ∉ L -> <{ s^x }> ⇛ <{ s'^x }>) ->
      <{ {x↦s}e }> ⇛ <{ {x↦s'}e }>) ->
  (forall x, x ∉ L -> <{ s^x }> ⇛* <{ s'^x }>) ->
  <{ {x↦s}e }> ⇛* <{ {x↦s'}e }>.
Proof.
  intros Hp H.
  simpl_cofin.
  match type of H with
  | ?s ⇛* ?s' => remember s; remember s'
  end.
  revert dependent s.
  induction H; intros; subst.
  - select (<{ _^_ }> = <{ _^_ }>) (fun H => apply open_inj in H).
    subst; reflexivity. fast_set_solver!!.
  - match goal with
    | H : <{ ?s^(fvar ?x) }> ⇛ ?e |- _ =>
        is_var e;
        assert (lc e) by eauto using pared_lc2;
        assert (e = open x (close x e)) by (by rewrite open_close)
    end.
    eapply rtc_l; [ | auto_apply ]; try set_shelve; eauto.

    eapply Hp.
    simpl_cofin.
    eapply pared_rename; try set_shelve; eauto. qauto.

  Unshelve.
  all: rewrite ?close_fv by auto; fast_set_solver!!.
Qed.

Lemma mpared_sound e1 e2 :
  mpared Σ e1 e2 ->
  lc e1 ->
  Σ ⊢ e1 ⇛* e2.
Proof.
  destruct 1; intros;
    repeat lc_inv;
    (* Generate [lc] and [woval] hypotheses from [⇛*] relation. *)
    do_hyps (fun H =>
               try lazymatch type of H with
                   | _ ⇛* _ =>
                       dup_hyp H (fun H =>
                                    apply mpared_lc in H; [ | solve [ eauto ] ])
                   | forall _, _ -> _ ⇛* _ =>
                       dup_hyp H (fun H =>
                                    eapply mpared_body in H;
                                    [ destruct H
                                    | solve [ eauto using body_intro ] ])
                   | woval _ =>
                       dup_hyp H (fun H =>
                                    eapply mpared_woval in H; [ | solve [ eauto ] ])
                   end);
    (* Consecutively apply [transitivity] such that any adjacent configurations
    differ in only one subexpression. *)
    let sol s s' e e' tac :=
      match eval pattern s in e with
      | ?f _ =>
          transitivity (f s'); [
            let x := fresh "x" in
            let H := fresh in
            pick_fresh as x;
            assert (forall s, f s = <{ {x↦s},(f x) }>) as H
                by (intros; simpl; rewrite ?decide_True by reflexivity;
                    rewrite ?subst_fresh by eauto; reflexivity);
            hnf in H;
            rewrite (H s);
            rewrite (H s');
            solve [ tac H ]
          | ]
      end in
    let rec go :=
      lazymatch goal with
      | H : ?s ⇛* ?s' |- ?e ⇛* ?e' =>
          sol s s' e e' ltac:(fun H => eapply mpared_subst1; eauto using lc);
          clear H; go
      | H : forall _, _ -> <{ ?s^_ }> ⇛* <{ ?s'^_ }> |- ?e ⇛* ?e' =>
          sol s s' e e' ltac:(fun H => eapply mpared_subst_body1; eauto;
                                     intros; rewrite <- ?H;
                                     eauto 10 using pared, lc);
          clear H; go
      (* Solve the last step. *)
      | |- _ => try reflexivity; apply rtc_once; eauto 10 using pared
      end in go.
Qed.

Lemma mpared_ocase b ω1 ω2 v e1 e2 e1' e2' L1 L2 :
  oval v ->
  otval ω1 -> otval ω2 ->
  body e1 -> body e2 ->
  (forall x, x ∉ L1 -> <{ e1^x }> ⇛* <{ e1'^x }>) ->
  (forall x, x ∉ L2 -> <{ e2^x }> ⇛* <{ e2'^x }>) ->
  <{ ~case [inj@b<(ω1 ~+ ω2)> v] of e1 | e2 }> ⇛* <{ ite b (e1'^v) (e2'^v) }>.
Proof.
  intros.
  select! (otval _) (fun H => use (ovalty_inhabited _ H)).
  select! (forall x, _ -> _ ⇛* _)
        (fun H => dup_hyp H (fun H => apply mpared_body in H; eauto)).
  select! (body _) (fun H => destruct H).
  etrans.
  - apply mpared_sound; eauto using lc, otval.
    econstructor; eauto using mpared.
  - case_split;
      (etrans; [ apply mpared_sound; eauto 10 using body_open_lc with lc;
                 econstructor; try reflexivity
               | reflexivity ]).
Qed.

Lemma mpared_tape v :
  oval v ->
  <{ tape v }> ⇛* v.
Proof.
  induction 1; try solve [ eauto 10 using mpared_sound, mpared with lc ].
  etrans.
  - apply mpared_sound; eauto with lc.
    econstructor; try reflexivity; eauto using oval_woval.
  - eauto 10 using mpared_sound, mpared with lc.
Qed.

End fix_gctx.

Create HintDb mpared discriminated.
#[export]
Hint Resolve mpared_sound : mpared.
#[export]
Hint Constructors mpared : mpared.
#[export]
Hint Resolve mpared_ocase : mpared.
#[export]
Hint Resolve mpared_tape : mpared.

Ltac relax_mpared :=
  match goal with
  | |- mpared ?Σ ?e _ =>
    refine (eq_ind _ (fun e' => mpared Σ e e') _ _ _)
  end.
