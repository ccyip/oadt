From idt Require Import all.
From oadt.lang_oadt Require Import
     base syntax semantics typing infrastructure
     values head dec mpared preservation progress.
Import syntax.notations semantics.notations typing.notations.

Implicit Types (b : bool) (x : atom) (L : aset).

#[local]
Coercion EFVar : atom >-> expr.

(** * Definitions *)

Section definitions.

(** ** Weak value erasure *)
Reserved Notation "'⟦' e '⟧'" (in custom oadt at level 20, format "'⟦' e '⟧'").
Reserved Notation "'⟦' e '⟧'" (at level 20, format "'⟦' e '⟧'").

(** This function checks if [<{ ~if e0 then e1 else e2 }>] is a weak value, and
returns the boolean discriminee if it is. *)
Definition is_oif_wval (e0 e1 e2 : expr) : option bool :=
  match e0 with
  | <{ [b] }> =>
      if decide (wval e1 /\ wval e2)
      then Some b
      else None
  | _ => None
  end.

(** This function erases all weak values in the expression [e], even if they are
under binders. It results in a canonical form that contains no "proper" weak
value, i.e., of the form [<{ ~if [b] then v1 else v2 }>]. The current version is
perhaps the "minimal" erasure needed to connect small-step and reveal semantics.
But it is also possible to erase a leaky conditional to its branches just if the
discriminee is a boxed boolean, regardless of it being a weak value or not. In
this case, reveal semantics may need some revision, and the crucial lemma
[reval_erase] would be significantly harder: each case would require a nested
induction. *)
Fixpoint erase_wval (e : expr) : expr :=
  match e with
  | <{ ~if e0 then e1 else e2 }> =>
    let e0' := ⟦e0⟧ in
    let e1' := ⟦e1⟧ in
    let e2' := ⟦e2⟧ in
    match is_oif_wval e0' e1' e2' with
    | Some b => <{ ite b e1' e2' }>
    | None => <{ ~if e0' then e1' else e2' }>
    end
  (* Congruence *)
  | <{ Π:{l}τ1, τ2 }> => <{ Π:{l}⟦τ1⟧, ⟦τ2⟧ }>
  | <{ \:{l}τ => e }> => <{ \:{l}⟦τ⟧ => ⟦e⟧ }>
  | <{ e1 e2 }> => <{ ⟦e1⟧ (⟦e2⟧) }>
  | <{ X@e }> => <{ X@⟦e⟧ }>
  | <{ let e1 in e2 }> => <{ let ⟦e1⟧ in ⟦e2⟧ }>
  | <{ s𝔹 e }> => <{ s𝔹 ⟦e⟧ }>
  | <{ if e0 then e1 else e2 }> => <{ if ⟦e0⟧ then ⟦e1⟧ else ⟦e2⟧ }>
  | <{ τ1 *{l} τ2 }> => <{ ⟦τ1⟧ *{l} ⟦τ2⟧ }>
  | <{ (e1, e2){l} }> => <{ (⟦e1⟧, ⟦e2⟧){l} }>
  | <{ π{l}@b e }> => <{ π{l}@b ⟦e⟧ }>
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


Context (Σ : gctx).

(** ** Reveal semantics *)
(** Reveal semantics is a big-step semantics in the reveal phase of an oblivious
computation. It does not match the small-step semantics completely, e.g., it
does not evaluate the "dead" branches unnecessarily. As a result, the reveal
semantics exhibits more behaviors than the small-step semantics, i.e. it may
terminate even if the small-step semantics does not. Nonetheless it is still
useful for reasoning about program behaviors when we assume they terminate,
because we can avoid reasoning about weak values and the nonconventional
small-step semantics. *)
Reserved Notation "e '↓' v" (at level 40).

Inductive reval : expr -> expr -> Prop :=
| REProd τ1 τ2 ω1 ω2 :
    τ1 ↓ ω1 ->
    τ2 ↓ ω2 ->
    <{ τ1 ~* τ2 }> ↓ <{ ω1 ~* ω2 }>
| REOSum τ1 τ2 ω1 ω2 :
    τ1 ↓ ω1 ->
    τ2 ↓ ω2 ->
    <{ τ1 ~+ τ2 }> ↓ <{ ω1 ~+ ω2 }>
| RETApp X e e2 τ v v2 :
    Σ !! X = Some (DOADT τ e) ->
    e2 ↓ v2 ->
    <{ e^v2 }> ↓ v ->
    <{ X@e2 }> ↓ v
| REApp e1 e2 v2 l τ e v :
    e1 ↓ <{ \:{l}τ => e }> ->
    e2 ↓ v2 ->
    <{ e^v2 }> ↓ v ->
    <{ e1 e2 }> ↓ v
| REFun x T e v :
    Σ !! x = Some (DFun T e) ->
    e ↓ v ->
    <{ gvar x }> ↓ v
| RELet e1 e2 v1 v :
    e1 ↓ v1 ->
    <{ e2^v1 }> ↓ v ->
    <{ let e1 in e2 }> ↓ v
| REIte e0 e1 e2 b v :
    e0 ↓ <{ b }> ->
    <{ ite b e1 e2 }> ↓ v ->
    <{ if e0 then e1 else e2 }> ↓ v
| REOIte e0 e1 e2 b v :
    e0 ↓ <{ [b] }> ->
    <{ ite b e1 e2 }> ↓ v ->
    <{ ~if e0 then e1 else e2 }> ↓ v
| REMux e0 e1 e2 b v :
    e0 ↓ <{ [b] }> ->
    <{ ite b e1 e2 }> ↓ v ->
    <{ mux e0 e1 e2 }> ↓ v
| RECase e0 e1 e2 b τ v0 v :
    e0 ↓ <{ inj@b<τ> v0 }> ->
    <{ ite b (e1^v0) (e2^v0) }> ↓ v ->
    <{ case e0 of e1 | e2 }> ↓ v
| REOCase e0 e1 e2 b ω1 ω2 v0 v :
    e0 ↓ <{ [inj@b<ω1 ~+ ω2> v0] }> ->
    <{ ite b (e1^v0) (e2^v0) }> ↓ v ->
    <{ ~case e0 of e1 | e2 }> ↓ v
| REInj b τ e v :
    e ↓ v ->
    <{ inj@b<τ> e }> ↓ <{ inj@b<⟦τ⟧> v }>
| REOInj b τ e ω v :
    τ ↓ ω ->
    e ↓ v ->
    otval ω ->
    oval v ->
    <{ ~inj@b<τ> e }> ↓ <{ [inj@b<ω> v] }>
| REPair l e1 e2 v1 v2 :
    e1 ↓ v1 ->
    e2 ↓ v2 ->
    <{ (e1, e2){l} }> ↓ <{ (v1, v2){l} }>
| REProj l b e v1 v2 :
    e ↓ <{ (v1, v2){l} }> ->
    <{ π{l}@b e }> ↓ <{ ite b v1 v2 }>
| REFold X e v :
    e ↓ v ->
    <{ fold<X> e }> ↓ <{ fold<X> v }>
| REUnfold X X' e v :
    e ↓ <{ fold <X'> v }> ->
    <{ unfold<X> e }> ↓ v
| RESec e b :
    e ↓ <{ b }> ->
    <{ s𝔹 e }> ↓ <{ [b] }>
| RETape e v :
    e ↓ v ->
    oval v ->
    <{ tape e }> ↓ v
| REVal v : val v -> v ↓ ⟦v⟧
| REOTVal ω : otval ω -> ω ↓ ω

where "e '↓' v" := (reval e v).

End definitions.

(** * Notations *)

Module Import notations.

Notation "'⟦' e '⟧'" := (erase_wval e) (in custom oadt at level 20,
                                           format "'⟦' e '⟧'").
Notation "'⟦' e '⟧'" := (erase_wval e) (at level 20, format "'⟦' e '⟧'").

Notation "Σ ⊨ e '↓' v" := (reval Σ e v) (at level 40).
Notation "e '↓' v" := (reval _ e v) (at level 40).

End notations.

(** * Inversion Lemmas *)

Ltac reval_inv :=
  match goal with
  | H : ?e ↓ _ |- _ => safe_inv e H
  end.

Tactic Notation "reval_inv" "*" :=
  repeat (reval_inv; repeat val_inv; repeat oval_inv; repeat otval_inv).

Section inversion.

Context (Σ : gctx).

#[local]
Set Default Proof Using "Type".

Ltac inv_solver := intros; reval_inv*; eauto 10 using reval, val.

Lemma reval_inv_oprod τ1 τ2 ω :
  <{ τ1 ~* τ2 }> ↓ ω ->
  exists ω1 ω2, ω = <{ ω1 ~* ω2 }> /\ τ1 ↓ ω1 /\ τ2 ↓ ω2.
Proof.
  inv_solver.
Qed.

Lemma reval_inv_osum τ1 τ2 ω :
  <{ τ1 ~+ τ2 }> ↓ ω ->
  exists ω1 ω2, ω = <{ ω1 ~+ ω2 }> /\ τ1 ↓ ω1 /\ τ2 ↓ ω2.
Proof.
  inv_solver.
Qed.

Lemma reval_inv_inj b τ e v :
  <{ inj@b<τ> e }> ↓ v ->
  exists v', v = <{ inj@b<⟦τ⟧> v' }> /\ e ↓ v'.
Proof.
  inv_solver.
Qed.

Lemma reval_inv_oinj b τ e v :
  <{ ~inj@b<τ> e }> ↓ v ->
  exists ω v', v = <{ [inj@b<ω> v'] }> /\ τ ↓ ω /\ e ↓ v' /\ otval ω /\ oval v'.
Proof.
  inv_solver.
Qed.

Lemma reval_inv_pair l e1 e2 v :
  <{ (e1, e2){l} }> ↓ v ->
  exists v1 v2, v = <{ (v1, v2){l} }> /\ e1 ↓ v1 /\ e2 ↓ v2.
Proof.
  inv_solver.
Qed.

Lemma reval_inv_fold X e v :
  <{ fold<X> e }> ↓ v ->
  exists v', v = <{ fold<X> v' }> /\ e ↓ v'.
Proof.
  inv_solver.
Qed.

End inversion.

(** * Tactics *)

Ltac reval_inv_lem e :=
  match e with
  | <{ _ * _ }> => reval_inv_oprod
  | <{ _ ~+ _ }> => reval_inv_osum
  | <{ inj@_<_> _ }> => reval_inv_inj
  | <{ ~inj@_<_> _ }> => reval_inv_oinj
  | <{ (_, _){_} }> => reval_inv_pair
  | <{ fold<_> _ }> => reval_inv_fold
  end.

Ltac reval_inv ::=
  match goal with
  | H : ?e ↓ _ |- _ =>
      let lem := reval_inv_lem e in
      apply lem in H; try simp_hyp H; subst
  | H : ?e ↓ _ |- _ => safe_inv e H
  end.

Ltac relax_reval :=
  match goal with
  | |- ?e ↓ _ =>
    refine (eq_ind _ (fun v => e ↓ v) _ _ _)
  end.

Ltac reval_intro :=
  relax_reval; [ econstructor | ].

(** * Theorems *)

Section theorems.

Context (Σ : gctx).

#[local]
Set Default Proof Using "Type".

(** ** Properties of [is_oif_wval] *)

Lemma is_oif_wval_inv_some e0 e1 e2 b :
  is_oif_wval e0 e1 e2 = Some b ->
  e0 = <{ [b] }> /\ wval e1 /\ wval e2.
Proof.
  destruct e0; simpl; intros; simplify_eq.
  case_decide; simplify_eq.
  eauto.
Qed.

Lemma is_oif_wval_inv_none e0 e1 e2 :
  is_oif_wval e0 e1 e2 = None ->
  ¬(wval e1 /\ wval e2) \/ expr_hd e0 <> HBoxedLit.
Proof.
  destruct e0; simpl; intros; simplify_eq; qauto.
Qed.

Ltac is_oif_wval_inv :=
  match goal with
  | H : is_oif_wval _ _ _ = Some _ |- _ =>
      apply is_oif_wval_inv_some in H; simpl in H;
      let H' := fresh in
      destruct H as [H' [??]]; try srewrite H'
  | H : is_oif_wval _ _ _ = None |- _ =>
      apply is_oif_wval_inv_none in H; simpl in H;
      try match type of H with
          | _ \/ HBoxedLit <> HBoxedLit =>
              destruct H; [ | simplify_eq ]
          end
  end.

Ltac case_is_oif_wval :=
  match goal with
  | |- context [ match is_oif_wval ?e0 ?e1 ?e2 with _ => _ end ] =>
      sdestruct (is_oif_wval e0 e1 e2)
  | H : context [ match is_oif_wval ?e0 ?e1 ?e2 with _ => _ end ] |- _ =>
      sdestruct (is_oif_wval e0 e1 e2)
  end.

Ltac simpl_is_oif_wval :=
  case_is_oif_wval; try is_oif_wval_inv.

Arguments is_oif_wval : simpl never.

(** ** Properties of [erase_wval] *)

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

Lemma erase_wval_val w :
  wval w ->
  val (⟦w⟧).
Proof.
  induction 1; eauto using val.

  simpl. simpl_is_oif_wval; qauto use: val_wval.
  rewrite erase_oval; eauto using val.
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

Lemma erase_idemp e :
  ⟦⟦e⟧⟧ = ⟦e⟧.
Proof.
  induction e; try scongruence.
  case_label; try scongruence.
  repeat (simpl; simpl_is_oif_wval); try scongruence; qauto.
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
  revert k. induction H; intros; try qauto ctrs: wval.
  rewrite open_lc; eauto using oval_lc, oval_wval.
Qed.

Lemma erase_open2 e s :
  <{ ⟦e^s⟧ }> = <{ ⟦⟦e⟧^s⟧ }>.
Proof.
  unfold open. generalize 0.
  induction e; simpl; intros; eauto; try congruence.
  case_split; try scongruence.

  repeat (simpl; simpl_is_oif_wval); try scongruence;
    select! (forall n, _ = _) (fun H => srewrite H; clear H);
    try qauto.
  hauto l: on use: erase_wval_wval, wval_open.
Qed.

Lemma erase_open e s :
  <{ ⟦e^s⟧ }> = <{ ⟦⟦e⟧^⟦s⟧⟧ }>.
Proof.
  qauto use: erase_open1, erase_open2.
Qed.

Lemma oval_open_inv e k s :
  ¬(oval s) ->
  oval <{ {k~>s}e }> ->
  oval e.
Proof.
  intros Hs.
  revert k.
  induction e; simpl; intros; try case_decide; try oval_inv;
    intuition eauto using oval.
Qed.

Lemma wval_open_inv e k s :
  ¬(wval s) ->
  wval <{ {k~>s}e }> ->
  wval e.
Proof.
  intro Hs.
  revert k.
  induction e; simpl; intros; try case_decide; try wval_inv; try oval_inv;
    intuition eauto using wval, oval.

  apply_open_hd; hauto ctrs: wval, oval.
  eauto 10 using wval, oval, oval_open_inv, oval_wval.
Qed.

Lemma erase_open_not_wval_ e s :
  ¬(wval (⟦s⟧)) ->
  <{ ⟦⟦e⟧^⟦s⟧⟧ }> = <{ ⟦e⟧^⟦s⟧ }>.
Proof.
  intros.
  unfold open. generalize 0.
  induction e; simpl; intros; eauto; try scongruence.
  - qauto use: erase_idemp.
  - case_split; try scongruence.
    repeat (simpl; simpl_is_oif_wval); try scongruence.
    + qauto.
    + exfalso.
      select! (forall n, _ = _) (fun H => srewrite H; clear H).
      intuition eauto using wval_open_inv.
      apply_open_hd; qauto ctrs: wval, oval.
Qed.

Lemma erase_open_not_wval e s :
  ¬(wval (⟦s⟧)) ->
  <{ ⟦e^s⟧ }> = <{ ⟦e⟧^⟦s⟧ }>.
Proof.
  hauto use: erase_open_not_wval_, erase_open.
Qed.

Lemma erase_open_atom e x :
  <{ ⟦e^x⟧ }> = <{ ⟦e⟧^x }>.
Proof.
  rewrite erase_open_not_wval; eauto using wval.
  qauto inv: wval, oval.
Qed.


(** ** Properties of [reval] *)

Lemma reval_val_inv v v' :
  v ↓ v' ->
  val v ->
  ⟦v⟧ = v'.
Proof.
  induction 1; intros; try val_inv; try oval_inv; qauto use: val_otval, oval_val.
Qed.

Lemma reval_otval_inv ω ω' :
  ω ↓ ω' ->
  otval ω ->
  ω = ω'.
Proof.
  induction 1; intros; try otval_inv; qauto use: val_otval.
Qed.

Theorem reval_deterministic e v1 v2 :
  e ↓ v1 ->
  e ↓ v2 ->
  v1 = v2.
Proof.
  intros H. revert v2.
  induction H; intros; reval_inv*;
    eauto using reval_val_inv, reval_otval_inv;
    hauto lq: on ctrs: reval use: oval_val.
Qed.

Lemma reval_idemp e v :
  e ↓ v ->
  v ↓ v.
Proof.
  induction 1; try hauto ctrs: reval, val, oval;
    reval_inv*;
    try case_split; eauto;
      reval_intro; eauto using val; try congruence.
  - rewrite erase_idemp. reflexivity.
  - eauto using erase_val_val.
  - eauto using erase_idemp.
Qed.

Lemma reval_fix_erase e v :
  e ↓ v ->
  v = ⟦v⟧.
Proof.
  induction 1; simpl; try scongruence use: erase_idemp;
    qauto use: erase_otval.
Qed.

Lemma reval_trans e v1 v2 :
  e ↓ v1 ->
  v1 ↓ v2 ->
  e ↓ v2.
Proof.
  intros.
  by replace v2 with v1 by eauto using reval_deterministic, reval_idemp.
Qed.

Lemma reval_wval_val e v :
  e ↓ v ->
  wval v ->
  val v.
Proof.
  qauto use: reval_fix_erase, erase_wval_val.
Qed.

Lemma reval_wval w :
  wval w ->
  w ↓ ⟦w⟧.
Proof.
  induction 1;
    first [ goal_contains <{ ~if _ then _ else _ }>
          | hauto l: on ctrs: reval, val ].

  simpl. simpl_is_oif_wval.
  - case_split; repeat (eauto using val, oval; reval_intro).
  - exfalso. eauto using erase_wval_wval.
Qed.

Lemma reval_oval v :
  oval v ->
  v ↓ v.
Proof.
  qauto use: reval_wval, oval_val, val_wval, erase_oval.
Qed.

Lemma reval_oval_inv v v' :
  v ↓ v' ->
  oval v ->
  v = v'.
Proof.
  eauto using reval_oval, reval_deterministic.
Qed.

Lemma reval_oval_oval v v' :
  v ↓ v' ->
  oval v ->
  oval v'.
Proof.
  intros. srewrite reval_oval_inv. eauto.
Qed.

Lemma reval_erase_val e :
  val (⟦e⟧) ->
  e ↓ ⟦e⟧.
Proof.
  induction e; simpl; intros; repeat val_inv; repeat oval_inv;
    try solve [ reval_intro; eauto using val, oval ].
  case_label; try simpl_is_oif_wval; repeat val_inv; repeat oval_inv.

  case_split; econstructor; eauto using val, oval.
Qed.

Lemma reval_erase_boxedlit e b :
  ⟦e⟧ = <{ [b] }> ->
  e ↓ <{ [b] }>.
Proof.
  intros H.
  relax_reval.
  apply reval_erase_val.
  rewrite H. eauto using val, oval.
  auto.
Qed.

Lemma reval_erase_otval e :
  otval (⟦e⟧) ->
  e ↓ ⟦e⟧.
Proof.
  induction e; simpl; intros; repeat otval_inv;
    eauto using reval, otval.

  case_label; try simpl_is_oif_wval; repeat otval_inv.
  case_split; econstructor; eauto using reval_erase_boxedlit.
Qed.

Lemma reval_erase_wval e :
  wval (⟦e⟧) ->
  e ↓ ⟦e⟧.
Proof.
  eauto using erase_wval_erase_val, reval_erase_val.
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

  simpl_is_oif_wval; eauto.
  right. repeat esplit; eauto using reval_erase_wval, reval_erase_boxedlit.
  qauto.
Qed.

(** This lemma is crucial. *)
Lemma reval_erase e1 e2 v :
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
                                  | try wval_inv; try oval_inv ]);
                simpl in H; simplify_eq
          ]
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
                try case_split; reval_intro; eauto; try congruence;
                match goal with
                | H : _ = ?e |- ?e = _ => rewrite <- H
                end; f_equal;
                (* Also possible to discharge this without
                [reval_deterministic]. In that case, induction hypothesis will
                be used with [erase_idemp] and [reval_val_inv] *)
                eauto using erase_wval_erase_val,
                  reval_erase_val,
                  oval_val,
                  reval_deterministic ].

  (* [REVal] *)
  - qauto l: on use: reval_erase_val, erase_val_val.

  (* [REOTVal] *)
  - hauto l: on use: erase_otval, reval_erase_otval.

  Unshelve.

  (* The most tricky [~if] case. *)
  simpl_is_oif_wval.

  + match goal with
    | H : ?e ↓ <{ [?b] }>, H' : ⟦?e⟧ = <{ [?b'] }> |- _ =>
        assert (<{ [b] }> = <{ [b'] }>)
          by eauto using reval_deterministic, reval_erase_boxedlit
    end.
    qauto.

  (* This part requires a nested induction: the current induction hypotheses
  are still needed. *)
  + match goal with
    | |- ?e ↓ _ => induction e
    end; simplify_eq; case_label; simplify_eq.
    simpl in *.
    simpl_is_oif_wval; simplify_eq; simp_hyps;
      reval_intro;
      eauto using reval_erase_boxedlit, reval_erase_wval;
      case_split; eauto.
Qed.

Lemma step_reval e e' v :
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
    try ectx_inv; reval_inv*; eauto using reval, val;
      repeat
        match goal with
        | |- context [<{ ite ?b _ _ }>] => destruct b
        | |- ?e ↓ _ =>
          head_constructor e; reval_intro; simpl
        | |- _ ↓ _ =>
          reval_inv*; eauto using reval_wval, reval_erase, erase_open1, erase_open
        | |- val _ => eauto using val, oval
        | |- ⟦_⟧ = _ => eauto using reval_deterministic, reval_wval
        | |- oval _ => eauto using oval
        | |- _ => eauto
        end; eauto using reval, oval_val, reval_oval.
  - select! (ovalty _ _) (fun H => apply ovalty_elim in H; try simp_hyp H);
      eauto using val, oval, otval.
  - case_split; reval_inv*; eauto.
  - eauto using reval_oval_oval.

  Unshelve.

  ectx_inv; reval_inv*;
    case_split; reval_inv*; econstructor;
      try match goal with
          | |- ?e ↓ _ => head_constructor e; reval_intro
          end;
      (* Need to discharge this first so the existential variables are not
      instantiated with wrong values. *)
      try match goal with
          | |- <{ _^_ }> ↓ _ => eauto
          end;
      eauto using reval_erase_boxedlit.
Qed.

Lemma mstep_reval e e' v :
  e -->* e' ->
  e' ↓ v ->
  e ↓ v.
Proof.
  induction 1; intros; eauto using step_reval.
Qed.

Theorem mstep_wval_reval e w :
  e -->* w ->
  wval w ->
  e ↓ ⟦w⟧.
Proof.
  eauto using mstep_reval, reval_wval.
Qed.

Theorem mstep_otval_reval e ω :
  e -->* ω ->
  otval ω ->
  e ↓ ω.
Proof.
  eauto using mstep_reval, reval.
Qed.

Theorem mstep_weak_confluent e w1 w2 :
  e -->* w1 ->
  wval w1 ->
  e -->* w2 ->
  wval w2 ->
  ⟦w1⟧ = ⟦w2⟧.
Proof.
  eauto using reval_deterministic, mstep_wval_reval.
Qed.

Context (Hwf : gctx_wf Σ).
(** From now on, we need the well-formedness of global context. *)
Set Default Proof Using "All".

Lemma erase_mpared e :
  lc e ->
  e ⇛* ⟦e⟧.
Proof.
  induction 1; simpl; try reflexivity;
    try case_split; eauto with mpared lc;
    try solve [ apply mpared_sound; eauto using lc;
                econstructor; eauto;
                intros; rewrite <- erase_open_atom; eauto ].

  (* [~if] case *)
  simpl_is_oif_wval;
    etrans;
    solve [ eapply mpared_sound; eauto using lc, mpared_lc;
            solve [ econstructor; eauto
                  | relax_mpared; [ econstructor; reflexivity | eauto ] ] ].
Qed.

#[local]
Hint Resolve body_open_lc : lc.

Lemma reval_mpared e v :
  e ↓ v ->
  lc e ->
  e ⇛* v.
Proof.
  induction 1; intros; try reflexivity;
    (* Generate [lc] facts first. *)
    repeat lc_inv; simp_hyps;
    try select! (_ ⇛* _) (fun H => dup_hyp H (fun H => apply mpared_lc in H; eauto));
    repeat lc_inv;
    try apply_gctx_wf;
    (* Solve simple cases. *)
    eauto using erase_mpared with mpared lc;
    (* Try apply induction hypotheses, then discharge the obligation. *)
    try (etrans; [ | select (lc _ -> _ ⇛* _) (fun H => apply H) ];
         eauto;
         match goal with
         | |- lc _ => try case_split; eauto with lc
         | |- _ ⇛* _ => eauto 10 with mpared lc
         end);
    (* Discharge more obligations. *)
    (etrans; [ apply mpared_sound; eauto using lc;
               solve [ econstructor; eauto with mpared ]
             | eauto 10 with mpared lc ]).

  (* [REOCase] *)
  otval_inv.
  eauto 10 with mpared lc.

  Unshelve.
  all: exact ∅.
Qed.

Lemma reval_lc e e' :
  lc e ->
  e ↓ e' ->
  lc e'.
Proof.
  eauto using mpared_lc, reval_mpared.
Qed.

Theorem reval_preservation Γ e l v τ :
  Γ ⊢ e :{l} τ ->
  e ↓ v ->
  Γ ⊢ v :{l} τ.
Proof.
  eauto using mpared_preservation, reval_mpared with lc.
Qed.

End theorems.

(** ** Alternative Definition *)

(** This equivalent definition of reveal semantics adds some side-conditions so
that the induction principle is stronger. It is useful in proving soundness. *)

Module kernel.

Reserved Notation "e '⇓' v" (at level 40).

(** We add side-conditions [v ⇓ v] for each sub-expression of the negatively
defined expressions, i.e., projection and unfold. *)
Inductive reval (Σ : gctx) : expr -> expr -> Prop :=
| REProj l b e v1 v2 :
    e ⇓ <{ (v1, v2){l} }> ->
    v1 ⇓ v1 -> v2 ⇓ v2 ->
    <{ π{l}@b e }> ⇓ <{ ite b v1 v2 }>
| REUnfold X X' e v :
    e ⇓ <{ fold <X'> v }> ->
    v ⇓ v ->
    <{ unfold<X> e }> ⇓ v

where "e '⇓' v" := (reval _ e v).

End kernel.

Ltac tsf_reval ctor R :=
  lazymatch ctor with
  | REProj => tsf_ctor_id kernel.REProj R
  | REUnfold => tsf_ctor_id kernel.REUnfold R
  | _ => tsf_ctor_id ctor R
  end.

MetaCoq Run (tsf_ind_gen_from
               reval "reval_alt"
               ltac:(tsf_ctors reval (append "A") tsf_reval)).

Module Import alt_notations.

Notation "e '⇓' v" := (reval_alt _ e v) (at level 40).

End alt_notations.

Ltac reval_alt_inv :=
  match goal with
  | H : ?e ⇓ _ |- _ => safe_inv e H
  end.

Tactic Notation "reval_alt_inv" "*" :=
  repeat (reval_alt_inv; repeat val_inv; repeat oval_inv; repeat otval_inv).

Ltac relax_reval_alt :=
  match goal with
  | |- ?e ⇓ _ =>
    refine (eq_ind _ (fun v => e ⇓ v) _ _ _)
  end.

Ltac reval_alt_intro :=
  relax_reval_alt; [ econstructor | ].

Section theorems.

Context (Σ : gctx).
Context (Hwf : gctx_wf Σ).
Set Default Proof Using "All".

Lemma reval_alt_idemp e v :
  e ⇓ v ->
  v ⇓ v.
Proof.
  induction 1; try hauto ctrs: reval_alt, val, oval;
    reval_alt_inv*;
    try case_split; eauto;
    reval_alt_intro; eauto; try congruence.
  - rewrite erase_idemp. reflexivity.
  - eauto using erase_val_val.
  - eauto using erase_idemp.
Qed.

Lemma reval_alt_complete e v :
  e ↓ v ->
  e ⇓ v.
Proof.
  induction 1; eauto using reval_alt;
    match goal with
    | H : _ ⇓ ?e |- _ =>
        head_constructor e; dup_hyp H (fun H => apply reval_alt_idemp in H)
    end;
    reval_alt_inv*; eauto using reval_alt;
    select! (⟦_⟧ = _) (fun H => srewrite H);
    econstructor; eauto;
    reval_alt_intro; eauto using val.
Qed.

Lemma reval_alt_sound e v :
  e ⇓ v ->
  e ↓ v.
Proof.
  induction 1; eauto using reval.
Qed.

Lemma reval_alt_consistent e v :
  e ↓ v <-> e ⇓ v.
Proof.
  qauto use: reval_alt_complete, reval_alt_sound.
Qed.

(** ** Soundness *)

Lemma reval_step e v v' :
  e ↓ v ->
  v -->! v' ->
  False.
Proof.
  intros H. revert dependent v'.
  apply reval_alt_complete in H.
  induction H; intros; try step_inv; eauto; try case_split; eauto.
  - eauto using wval_step, val_wval, erase_val_val.
  - eauto using otval_step.
Qed.

Lemma reval_nf e v :
  e ↓ v ->
  nf (step Σ) v.
Proof.
  sfirstorder use: reval_step.
Qed.

Theorem reval_soundness e l v τ :
  ∅ ⊢ e :{l} τ ->
  e ↓ v ->
  val v.
Proof.
  intros.
  assert (∅ ⊢ v :{l} τ) as L by eauto using reval_preservation.
  apply progress_weak in L; eauto.
  destruct L; simp_hyps; eauto using reval_wval_val.
  exfalso. eauto using reval_step.
Qed.

Corollary reval_soundness_strong e l v τ :
  ∅ ⊢ e :{l} τ ->
  e ↓ v ->
  val v /\ ∅ ⊢ v :{l} τ.
Proof.
  eauto using reval_soundness, reval_preservation.
Qed.

End theorems.
