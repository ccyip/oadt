From oadt Require Import idt.
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.equivalence.
From oadt Require Import lang_oadt.head.

Import syntax.notations.
Import typing.notations.

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

Lemma mpared_woval ω τ :
  woval ω ->
  ω ⇛* τ ->
  woval τ.
Proof.
  eapply rtc_preserve; eauto using pared_woval.
Qed.

Lemma mpared_open_lc e e' L1 L2 :
  (forall x, x ∉ L1 -> <{ e^x }> ⇛* <{ e'^x }>) ->
  (forall x, x ∉ L2 -> lc <{ e^x }>) ->
  exists L, forall x, x ∉ L -> lc <{ e'^x }>.
Proof.
  intros. eexists. simpl_cofin. eauto using mpared_lc.
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
                                    eapply mpared_open_lc in H;
                                    [ simp_hyp H
                                    | solve [ eauto ] ])
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

End fix_gctx.

Create HintDb mpared discriminated.
#[export]
Hint Resolve mpared_sound : mpared.
#[export]
Hint Constructors mpared : mpared.
