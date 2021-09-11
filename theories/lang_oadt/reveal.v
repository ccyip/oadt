From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.values.
From oadt Require Import lang_oadt.head.

Import syntax.notations.

Implicit Types (b : bool).

#[local]
Coercion EFVar : atom >-> expr.

(** * Definitions *)

(** ** Decision procedures *)

Section dec.

Ltac t :=
  solve [ repeat
            (try match reverse goal with
                 | H : sumbool _ _ |- _ => destruct H
                 end;
             try solve [ left; econstructor; assumption
                       | right; inversion 1; subst; contradiction ]) ].

#[global]
Instance otval_dec ω : Decision (otval ω).
Proof.
  hnf. induction ω; try t; try case_label; try t.
Defined.

#[global]
Instance oval_dec v : Decision (oval v).
Proof.
  hnf. induction v; try t; try case_label; try t.

  match goal with
  | H : context [ oval ?ω] |- context [<{ [inj@_<(?ω)> _] }>] =>
    clear H; destruct (decide (otval ω)); try t
  end.
Defined.

#[global]
Instance wval_dec v : Decision (wval v).
Proof.
  hnf. induction v; try t; try case_label; try t.
  - match goal with
    | H : context [ wval ?v] |- context [<{ ~if ?v then _ else _ }>] =>
      clear H; destruct v; try t
    end.
  - match goal with
    | H : context [ wval ?ω], H' : context [ wval ?v ] |-
      context [<{ [inj@_<(?ω)> ?v] }>] =>
      clear H; clear H';
        destruct (decide (otval ω)); try t;
        destruct (decide (oval v)); try t
    end.
Defined.

End dec.

(** ** Weak value erasure *)
(** This function erases all weak values in the expression [e], even if they are
under binders. This erasure results in a canonical form that has no weak values
in the form of [~if .. then .. else ..] in it. *)
Reserved Notation "'⟦' e '⟧'" (in custom oadt at level 20, format "'⟦' e '⟧'").
Reserved Notation "'⟦' e '⟧'" (at level 20, format "'⟦' e '⟧'").

Fixpoint erase_wval (e : expr) : expr :=
  match e with
  | <{ ~if e0 then e1 else e2 }> =>
    let e0' := ⟦e0⟧ in
    let e1' := ⟦e1⟧ in
    let e2' := ⟦e2⟧ in
    if decide (wval e1' /\ wval e2')
    then if decide (e0' = <{ [true] }>)
         then e1'
         else if decide (e0' = <{ [false] }>)
              then e2'
              else <{ ~if e0' then e1' else e2' }>
    else <{ ~if e0' then e1' else e2' }>
  (* Congruence *)
  | <{ Π:{l}τ1, τ2 }> => <{ Π:{l}⟦τ1⟧, ⟦τ2⟧ }>
  | <{ \:{l}τ => e }> => <{ \:{l}⟦τ⟧ => ⟦e⟧ }>
  | <{ e1 e2 }> => <{ ⟦e1⟧ (⟦e2⟧) }>
  | <{ X@e }> => <{ X@⟦e⟧ }>
  | <{ let e1 in e2 }> => <{ let ⟦e1⟧ in ⟦e2⟧ }>
  | <{ s𝔹 e }> => <{ s𝔹 ⟦e⟧ }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} ⟦e0⟧ then ⟦e1⟧ else ⟦e2⟧ }>
  | <{ τ1 * τ2 }> => <{ ⟦τ1⟧ * ⟦τ2⟧ }>
  | <{ (e1, e2) }> => <{ (⟦e1⟧, ⟦e2⟧) }>
  | <{ π@b e }> => <{ π@b ⟦e⟧ }>
  | <{ τ1 +{l} τ2 }> => <{ ⟦τ1⟧ +{l} ⟦τ2⟧ }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<⟦τ⟧> ⟦e⟧ }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} ⟦e0⟧ of ⟦e1⟧ | ⟦e2⟧ }>
  | <{ fold<X> e }> => <{ fold<X> ⟦e⟧ }>
  | <{ unfold<X> e }> => <{ unfold<X> ⟦e⟧ }>
  | <{ tape e }> => <{ tape ⟦e⟧ }>
  | <{ mux e0 e1 e2 }> => <{ mux ⟦e0⟧ ⟦e1⟧ ⟦e2⟧ }>
  | _ => e
  end

where "'⟦' e '⟧'" := (erase_wval e) (in custom oadt)
  and "'⟦' e '⟧'" := (erase_wval e).


Section reveal.

Context (Σ : gctx).

(** ** Unsafe semantics *)
(** Unsafe semantics is the big-step semantics corresponding to the small-step
semantics defined by [step]. It ignores the secure constructs and evaluates the
expressions to values. While this semantics is not safe, it is a much easier
machineary to reason about program logic. This semantics is meant to be
equivalent to the small-step semantics (in terms of program behavior), so it
will evaluate the "dead" branches in the oblivious constructs. *)
Reserved Notation "e '↓' v" (at level 40).

Inductive ueval : expr -> expr -> Prop :=
| UEProd τ1 τ2 ω1 ω2 :
    τ1 ↓ ω1 ->
    τ2 ↓ ω2 ->
    <{ τ1 * τ2 }> ↓ <{ ω1 * ω2 }>
| UEOSum τ1 τ2 ω1 ω2 :
    τ1 ↓ ω1 ->
    τ2 ↓ ω2 ->
    <{ τ1 ~+ τ2 }> ↓ <{ ω1 ~+ ω2 }>
| UETApp X e e2 τ v v2 :
    Σ !! X = Some (DOADT τ e) ->
    e2 ↓ v2 ->
    <{ e^v2 }> ↓ v ->
    <{ X@e2 }> ↓ v
| UEApp e1 e2 v2 l τ e v :
    e1 ↓ <{ \:{l}τ => e }> ->
    e2 ↓ v2 ->
    <{ e^v2 }> ↓ v ->
    <{ e1 e2 }> ↓ v
| UEFun x T e v :
    Σ !! x = Some (DFun T e) ->
    e ↓ v ->
    <{ gvar x }> ↓ v
| UELet e1 e2 v1 v :
    e1 ↓ v1 ->
    <{ e2^v1 }> ↓ v ->
    <{ let e1 in e2 }> ↓ v
| UEIte e0 e1 e2 b v :
    e0 ↓ <{ b }> ->
    <{ ite b e1 e2 }> ↓ v ->
    <{ if e0 then e1 else e2 }> ↓ v
| UEOIte e0 e1 e2 b v1 v2 :
    e0 ↓ <{ [b] }> ->
    e1 ↓ v1 ->
    e2 ↓ v2 ->
    <{ ~if e0 then e1 else e2 }> ↓ <{ ite b v1 v2 }>
| UEMux e0 e1 e2 b v1 v2 :
    e0 ↓ <{ [b] }> ->
    e1 ↓ v1 ->
    e2 ↓ v2 ->
    <{ mux e0 e1 e2 }> ↓ <{ ite b v1 v2 }>
| UEInj b τ e v :
    e ↓ v ->
    <{ inj@b<τ> e }> ↓ <{ inj@b<⟦τ⟧> v }>
| UEOInj b τ e ω v :
    τ ↓ ω ->
    e ↓ v ->
    otval ω ->
    oval v ->
    <{ ~inj@b<τ> e }> ↓ <{ [inj@b<ω> v] }>
| UECase e0 e1 e2 b τ v0 v :
    e0 ↓ <{ inj@b<τ> v0 }> ->
    <{ ite b (e1^v0) (e2^v0) }> ↓ v ->
    <{ case e0 of e1 | e2 }> ↓ v
| UEOCase e0 e1 e2 b ω1 ω2 v v1 v1' v2 v2' :
    e0 ↓ <{ [inj@b<ω1 ~+ ω2> v] }> ->
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    <{ ite b (e1^v) (e1^v1) }> ↓ v1' ->
    <{ ite b (e2^v2) (e2^v) }> ↓ v2' ->
    <{ ~case e0 of e1 | e2 }> ↓ <{ ite b v1' v2' }>
| UEPair e1 e2 v1 v2 :
    e1 ↓ v1 ->
    e2 ↓ v2 ->
    <{ (e1, e2) }> ↓ <{ (v1, v2) }>
| UEProj b e v1 v2 :
    e ↓ <{ (v1, v2) }> ->
    <{ π@b e }> ↓ <{ ite b v1 v2 }>
| UEFold X e v :
    e ↓ v ->
    <{ fold<X> e }> ↓ <{ fold<X> v }>
| UEUnfold X X' e v :
    e ↓ <{ fold <X'> v }> ->
    <{ unfold<X> e }> ↓ v
| UESec e b :
    e ↓ <{ b }> ->
    <{ s𝔹 e }> ↓ <{ [b] }>
| UETape e v :
    e ↓ v ->
    (* oval v -> *)
    <{ tape e }> ↓ v
| UEVal v : val v -> v ↓ ⟦v⟧
| UEOTVal ω : otval ω -> ω ↓ ω

where "e '↓' v" := (ueval e v).

(** ** Reveal semantics *)
(** Reveal semantics is a big-step semantics in the reveal phase of an oblivious
computation. It reveals all the secrets like the unsafe semantics. However, as
it is meant to be used in the reveal phase, it does not have to match the safe
semantics completely, e.g., it does not evaluate the "dead" branches
unnecessarily. As a result, the reveal semantics exhibits more behaviors, i.e.
it may terminate even if the safe semantics does not. *)
Reserved Notation "e '⇓' v" (at level 40).

Inductive reval : expr -> expr -> Prop :=
| REProd τ1 τ2 ω1 ω2 :
    τ1 ⇓ ω1 ->
    τ2 ⇓ ω2 ->
    <{ τ1 * τ2 }> ⇓ <{ ω1 * ω2 }>
| REOSum τ1 τ2 ω1 ω2 :
    τ1 ⇓ ω1 ->
    τ2 ⇓ ω2 ->
    <{ τ1 ~+ τ2 }> ⇓ <{ ω1 ~+ ω2 }>
| RETApp X e e2 τ v v2 :
    Σ !! X = Some (DOADT τ e) ->
    e2 ⇓ v2 ->
    <{ e^v2 }> ⇓ v ->
    <{ X@e2 }> ⇓ v
| REApp e1 e2 v2 l τ e v :
    e1 ⇓ <{ \:{l}τ => e }> ->
    e2 ⇓ v2 ->
    <{ e^v2 }> ⇓ v ->
    <{ e1 e2 }> ⇓ v
| REFun x T e v :
    Σ !! x = Some (DFun T e) ->
    e ⇓ v ->
    <{ gvar x }> ⇓ v
| RELet e1 e2 v1 v :
    e1 ⇓ v1 ->
    <{ e2^v1 }> ⇓ v ->
    <{ let e1 in e2 }> ⇓ v
| REIte e0 e1 e2 b v :
    e0 ⇓ <{ b }> ->
    <{ ite b e1 e2 }> ⇓ v ->
    <{ if e0 then e1 else e2 }> ⇓ v
| REOIte e0 e1 e2 b v :
    e0 ⇓ <{ [b] }> ->
    <{ ite b e1 e2 }> ⇓ v ->
    <{ ~if e0 then e1 else e2 }> ⇓ v
| REMux e0 e1 e2 b v :
    e0 ⇓ <{ [b] }> ->
    <{ ite b e1 e2 }> ⇓ v ->
    <{ mux e0 e1 e2 }> ⇓ v
| RECase e0 e1 e2 b τ v0 v :
    e0 ⇓ <{ inj@b<τ> v0 }> ->
    <{ ite b (e1^v0) (e2^v0) }> ⇓ v ->
    <{ case e0 of e1 | e2 }> ⇓ v
| REOCase e0 e1 e2 b τ v0 v :
    e0 ⇓ <{ [inj@b<τ> v0] }> ->
    <{ ite b (e1^v0) (e2^v0) }> ⇓ v ->
    <{ ~case e0 of e1 | e2 }> ⇓ v
| REInj b τ e v :
    e ⇓ v ->
    <{ inj@b<τ> e }> ⇓ <{ inj@b<⟦τ⟧> v }>
| REOInj b τ e ω v :
    τ ⇓ ω ->
    e ⇓ v ->
    otval ω ->
    oval v ->
    <{ ~inj@b<τ> e }> ⇓ <{ [inj@b<ω> v] }>
| REPair e1 e2 v1 v2 :
    e1 ⇓ v1 ->
    e2 ⇓ v2 ->
    <{ (e1, e2) }> ⇓ <{ (v1, v2) }>
| REProj b e v1 v2 :
    e ⇓ <{ (v1, v2) }> ->
    <{ π@b e }> ⇓ <{ ite b v1 v2 }>
| REFold X e v :
    e ⇓ v ->
    <{ fold<X> e }> ⇓ <{ fold<X> v }>
| REUnfold X X' e v :
    e ⇓ <{ fold <X'> v }> ->
    <{ unfold<X> e }> ⇓ v
| RESec e b :
    e ⇓ <{ b }> ->
    <{ s𝔹 e }> ⇓ <{ [b] }>
| RETape e v :
    e ⇓ v ->
    (* oval v -> *)
    <{ tape e }> ⇓ v
| REVal v : val v -> v ⇓ ⟦v⟧
| REOTVal ω : otval ω -> ω ⇓ ω

where "e '⇓' v" := (reval e v).


(** * Theorems *)

Notation "e '-->!' e'" := (step Σ e e') (at level 40,
                                         e' custom oadt at level 0).

Notation "e '-->*' e'" := (rtc (step Σ) e e')
                            (at level 40,
                             e' custom oadt at level 0).

#[local]
Set Default Proof Using "Type".

Ltac ueval_inv :=
  match goal with
  | H : ?e ↓ _ |- _ => safe_inv e H
  end.

Tactic Notation "ueval_inv" "*" :=
  repeat (ueval_inv; repeat val_inv; repeat otval_inv).

Ltac relax_ueval :=
  match goal with
  | |- ?e ↓ _ =>
    refine (eq_ind _ (fun v => e ↓ v) _ _ _)
  end.

Ltac ueval_intro :=
  relax_ueval; [ econstructor | ].


(** ** Properties of [erase_wval] *)

Lemma erase_wval_val w :
  wval w ->
  val (⟦w⟧).
Proof.
  induction 1; eauto using val.

  simpl. repeat case_decide; eauto.
  destruct (_ : bool); contradiction.
  qauto use: val_wval.
Qed.

Lemma erase_val_val v :
  val v ->
  val (⟦v⟧).
Proof.
  eauto using erase_wval_val, val_wval.
Qed.

Lemma erase_wval_wval v :
  wval v ->
  wval (⟦v⟧).
Proof.
  eauto using erase_wval_val, val_wval.
Qed.

Lemma erase_otval ω :
  otval ω ->
  ⟦ω⟧ = ω.
Proof.
  induction 1; qauto.
Qed.

Lemma erase_oval v :
  oval v ->
  ⟦v⟧ = v.
Proof.
  induction 1; qauto.
Qed.

Lemma erase_idemp e :
  ⟦⟦e⟧⟧ = ⟦e⟧.
Proof.
  induction e; try scongruence.
  case_label; try scongruence.
  repeat (simpl; repeat case_decide; eauto; try scongruence).
Qed.

Lemma erase_wval_erase_val e :
  wval (⟦e⟧) ->
  val (⟦e⟧).
Proof.
  intros H.
  rewrite <- erase_idemp.
  eauto using erase_wval_val.
Qed.

Lemma erase_open1 e s :
  <{ ⟦e^s⟧ }> = <{ ⟦e^⟦s⟧⟧ }>.
Proof.
  unfold open. generalize 0.
  induction e; simpl; intros; try congruence;
    hauto l: on use: erase_idemp.
Qed.

Lemma wval_open e k s :
  wval e ->
  wval <{ {k~>s}e }>.
Proof.
  intros H.
  revert k. induction H; intros; qauto ctrs: wval.
Qed.

Lemma erase_open2 e s :
  <{ ⟦e^s⟧ }> = <{ ⟦⟦e⟧^s⟧ }>.
Proof.
  unfold open. generalize 0.
  induction e; simpl; intros; eauto; try congruence.
  case_split; try scongruence.

  repeat destruct (decide (wval _ /\ wval _));
    try match goal with
        | H : wval _ /\ wval _, H' : ¬ (wval (⟦<{ {_~>_}_ }>⟧) /\ wval _) |- _ =>
          contradict H'
        end;
    repeat (repeat case_decide; try scongruence; simpl); try qauto q: on.

  simp_hyps.
  repeat match goal with
         | H : forall _, _ |- _ => rewrite H
         end.
  hauto l: on use: erase_wval_wval, wval_open.
Qed.

Lemma erase_open e s :
  <{ ⟦e^s⟧ }> = <{ ⟦⟦e⟧^⟦s⟧⟧ }>.
Proof.
  qauto use: erase_open1, erase_open2.
Qed.


(** ** Properties of [ueval] *)

Lemma ueval_val_inv v v' :
  v ↓ v' ->
  val v ->
  ⟦v⟧ = v'.
Proof.
  induction 1; intros; try val_inv; try qauto use: val_otval.
Qed.

Lemma ueval_otval_inv ω ω' :
  ω ↓ ω' ->
  otval ω ->
  ω = ω'.
Proof.
  induction 1; intros; try otval_inv; qauto use: val_otval.
Qed.

Theorem ueval_deterministic e v1 v2 :
  e ↓ v1 ->
  e ↓ v2 ->
  v1 = v2.
Proof.
  intros H. revert v2.
  induction H; intros; ueval_inv*;
    eauto using ueval_val_inv, ueval_otval_inv;
    hauto lq: on ctrs: ueval.
Qed.

Lemma ueval_idemp e v :
  e ↓ v ->
  v ↓ v.
Proof.
  induction 1; try hauto ctrs: ueval, val;
    ueval_inv*;
    try case_split; eauto;
      ueval_intro; eauto; try congruence.
  - rewrite erase_idemp. reflexivity.
  - eauto using erase_val_val.
  - eauto using erase_idemp.
Qed.

Lemma ueval_wval w :
  wval w ->
  w ↓ ⟦w⟧.
Proof.
  induction 1;
    first [ goal_contains <{ ~if _ then _ else _ }>
          | hauto l: on ctrs: ueval, val ].

  simpl.
  repeat case_decide; simp_hyps.

  1-2: repeat (ueval_intro; eauto using val); reflexivity.

  destruct (_ : bool); contradiction.

  exfalso. eauto using erase_wval_wval.
Qed.

Lemma ueval_oval v :
  oval v ->
  v ↓ v.
Proof.
  qauto use: ueval_wval, oval_val, val_wval, erase_oval.
Qed.

Lemma ueval_erase_val e :
  val (⟦e⟧) ->
  e ↓ ⟦e⟧.
Proof.
  induction e; simpl; intros Hv; sinvert Hv;
    try solve [ ueval_intro; eauto using val ];
    case_label; simplify_eq;
      repeat case_decide; simplify_eq; simp_hyps;
        ueval_intro;
          (* Apply induction hypotheses. *)
          try (goal_is (_ ↓ _); first [ auto_apply | relax_ueval; auto_apply ]);
          eauto;
          try (match goal with
               | H : ?e = _ |- val ?e => rewrite H
               end; econstructor);
          rewrite <- erase_idemp; eauto using erase_wval_val.
Qed.

Lemma ueval_erase_otval e :
  otval (⟦e⟧) ->
  e ↓ ⟦e⟧.
Proof.
  induction e; simpl; intros Hv; sinvert Hv;
    eauto using ueval, otval;
    case_label; simplify_eq;
      repeat case_decide; simplify_eq; simp_hyps;
        match goal with
        | H : _ = ?e, H' : wval ?e |- _ =>
          rewrite <- H in H'; sinvert H'
        end.
Qed.

Lemma ueval_erase_boxedlit e b :
  ⟦e⟧ = <{ [b] }> ->
  e ↓ <{ [b] }>.
Proof.
  intros H.
  relax_ueval.
  apply ueval_erase_val.
  rewrite H. constructor.
  auto.
Qed.

Lemma ueval_erase_wval e :
  wval (⟦e⟧) ->
  e ↓ ⟦e⟧.
Proof.
  eauto using erase_wval_erase_val, ueval_erase_val.
Qed.

Lemma erase_inv e e' :
  e' = ⟦e⟧ ->
  expr_hd e = expr_hd e' \/
  (wval e' /\
   exists b e0 e1 e2,
     e = <{ ~if e0 then e1 else e2 }> /\
     e0 ↓ <{ [b] }> /\
     e1 ↓ ⟦e1⟧ /\
     e2 ↓ ⟦e2⟧ /\
     e' = <{ ite b ⟦e1⟧ ⟦e2⟧ }>).
Proof.
  destruct e; intros; subst; simpl; try solve [ left; reflexivity ].
  case_label; try solve [ left; reflexivity ].

  repeat case_decide; simp_hyps; eauto;
    right; repeat esplit; eauto using ueval_erase_wval, ueval_erase_boxedlit.
Qed.

(** This lemma is crucial. *)
Lemma ueval_erase e1 e2 v :
  e1 ↓ v ->
  ⟦e1⟧ = ⟦e2⟧ ->
  e2 ↓ v.
Proof.
  intros H. revert e2.
  induction H; intros; simpl in *;
    try
      match goal with
      | H : ?e = ⟦_⟧ |- _ =>
        (* [~if] case is quite tricky. Handle it later. *)
        first [ match e with
                | context [ <{ ~if _ then _ else _ }> ] => shelve
                end
              | head_constructor e;
                dup_hyp H (fun H => apply erase_inv in H; destruct H as [| [? ?]];
                                  [ expr_hd_inv in H
                                  | try wval_inv ]);
                simpl in H; try simp_hyp H ]
      end;
    try solve [ econstructor; eauto; try case_split; eauto;
                (* Handle binders. *)
                auto_apply;
                match goal with
                | |- <{ ⟦?e1^_⟧ }> = <{ ⟦?e2^_⟧ }> =>
                  rewrite (erase_open2 e1); rewrite (erase_open2 e2)
                end; congruence
              (* Weak value cases. *)
              | simp_hyps; subst;
                ueval_intro; eauto; try congruence;
                match goal with
                | H : _ = ?e |- ?e = _ => rewrite <- H
                end; f_equal;
                (* Also possible to discharge this without
                [ueval_deterministic]. In that case, induction hypothesis will
                be used with [erase_idemp] and [ueval_val_inv] *)
                eauto using erase_wval_erase_val,
                ueval_erase_val,
                ueval_deterministic ].

  (* [UEVal] *)
  - qauto l: on use: ueval_erase_val, erase_val_val.

  (* [UEOTVal] *)
  - hauto l: on use: erase_otval, ueval_erase_otval.

  Unshelve.

  (* The most tricky [~if] case. *)
  match goal with
  | H : ?e = ⟦?e'⟧, H' : ?e0 ↓ <{ [?b] }> |- _ =>
    match e with
    | context [ <{ ~if ⟦e0⟧ then ⟦?e1⟧ else ⟦?e2⟧ }> ] =>
      (* A cut that reduces the number of cases. *)
      let L := fresh in
      assert ((⟦e0⟧ = <{ [b] }> /\ ⟦e'⟧ = <{ ite b ⟦e1⟧ ⟦e2⟧ }>) \/
              <{ ~if ⟦e0⟧ then ⟦e1⟧ else ⟦e2⟧ }> = ⟦e'⟧) as L;
        [ | clear H; destruct L ]
    end
  end. {
    repeat case_decide; simplify_eq; simp_hyps; eauto; left;
      match goal with
      | H : ?e = <{ [?b'] }> |- ?e = <{ [?b] }> /\ _ =>
        let L := fresh in
        assert (<{ [b] }> = <{ [b'] }>) as L
            by eauto using ueval_deterministic, ueval_erase_boxedlit;
          sinvert L; subst; eauto
      end.
  }

  qauto.

  (* This part requires a nested induction: the current induction hypotheses
  are still needed. *)
  match goal with
  | |- ?e ↓ _ => induction e
  end; simplify_eq; case_label; simplify_eq.
  simpl in *.
  repeat case_decide; simplify_eq; simp_hyps;
    ueval_intro; eauto;
      eauto using ueval_erase_boxedlit, ueval_erase_wval.
Qed.

Lemma ueval_step e e' v :
  e -->! e' ->
  e' ↓ v ->
  e ↓ v.
Proof.
  intros H. revert v.
  induction H; intros;
    (* Handle leaky context later. *)
    try match goal with
        | H : lectx _ |- _ => shelve
        end;
    try ectx_inv; ueval_inv*; eauto using ueval, val;
      repeat
        match goal with
        | |- ?e ↓ _ =>
          head_constructor e; ueval_intro; simpl
        | |- _ ↓ _ =>
          eauto using ueval_wval, ueval_erase, erase_open1, erase_open
        | |- val _ => eauto using val
        | |- <{ ite _ ⟦_⟧ ⟦_⟧ }> = _ =>
          try case_split; eauto using ueval_deterministic, ueval_wval
        | |- _ => eauto
        end.
  - eauto using ueval.
  - eauto using ueval_oval.
  - case_split; eauto using ueval_erase, erase_open1.
  - select! (ovalty _ _) (fun H => apply ovalty_elim in H; try simp_hyp H);
      eauto using val, otval.

  Unshelve.

  ectx_inv; ueval_inv*;
    case_split; econstructor;
      try match goal with
          | |- ?e ↓ _ => head_constructor e; ueval_intro
          end;
      (* Need to discharge this first so the existential variables are not
      instantiated with wrong values. *)
      try match goal with
          | |- <{ _^_ }> ↓ _ => eauto
          end;
      eauto using ueval_erase_boxedlit.
Qed.

Lemma ueval_multistep e e' v :
  e -->* e' ->
  e' ↓ v ->
  e ↓ v.
Proof.
  induction 1; intros; eauto using ueval_step.
Qed.

Theorem ueval_multistep_nf e w :
  e -->* w ->
  wval w ->
  e ↓ ⟦w⟧.
Proof.
  eauto using ueval_multistep, ueval_wval.
Qed.

End reveal.
