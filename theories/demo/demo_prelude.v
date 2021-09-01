(** This file contains (possibly dirty and hacky) auxiliary definitions, lemmas
and tactics to ease the encoding of examples. It also contains the axiomatized
primitive integers. *)
(* Don't understand why Coq doesn't allow me to use the name "prelude.v" even
though another file with the same name lives in a different path. *)
From oadt Require Import prelude.
From Coq Require Import Int63.Int63.
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.typing.
From oadt Require Import lang_oadt.admissible.
From oadt Require Import lang_oadt.infrastructure.
From oadt Require Import lang_oadt.inversion.
From oadt Require Import lang_oadt.preservation.
From oadt Require Import lang_oadt.equivalence.
From oadt Require Import lang_oadt.values.

#[local]
Set Default Proof Using "Type".

(** * Notations *)

Module notations.

Export syntax.notations.
Export semantics.notations.
Export typing.notations.

(** Sometimes we want a more explicit notation. *)
Notation "'$' n" := (EBVar n) (in custom oadt at level 0,
                                  n constr at level 0,
                                  format "'$' n").
Notation "'!' x" := (EGVar x) (in custom oadt at level 0,
                                  x custom oadt at level 0,
                                  format "'!' x").
Notation "'#' x" := (EFVar x) (in custom oadt at level 0,
                                  x constr at level 0,
                                  format "'#' x").

(** Alternatives to π1 and π2. *)
Notation "e '.1'" := <{ π1 e }> (in custom oadt at level 1,
                                    format "e '.1'").
Notation "e '.2'" := <{ π2 e }> (in custom oadt at level 1,
                                    format "e '.2'").

(** Global definitions. *)
Notation "D" := D (in custom oadt_def at level 0, D constr at level 0).
Notation "( D )" := D (in custom oadt_def, D at level 99).
Notation "'data' X := e" := (X, DADT e) (in custom oadt_def at level 0,
                                            X custom oadt at level 99,
                                            e custom oadt at level 99).
Notation "'obliv' X ( : τ ) := e" := (X, DOADT τ e)
                                       (in custom oadt_def at level 0,
                                           X custom oadt at level 0,
                                           τ custom oadt at level 99,
                                           e custom oadt at level 99,
                                           format "obliv  X  ( : τ )  :=  e").
Notation "'def' x ':{' l '}' τ := e" := (x, DFun (l, τ) e)
                                          (in custom oadt_def at level 0,
                                              x custom oadt at level 0,
                                              τ custom oadt at level 99,
                                              e custom oadt at level 99,
                                              format "'def'  x  ':{' l '}'  τ  :=  e").
Notation "[{ x }]" := (cons x nil)
                        (x custom oadt_def at level 99).
Notation "[{ x ; y ; .. ; z }]" := (cons x (cons y .. (cons z nil) ..))
                                     (x custom oadt_def at level 0,
                                      y custom oadt_def at level 99,
                                      z custom oadt_def at level 99,
                                      format "[{ '[v  ' '/' x ; '/' y ; '/' .. ; '/' z ']' '//' }]").

End notations.

Import notations.

(** * Alternative step rules *)

(** An equivalent step relation that is easier to use in examples. *)
Section step.

Context (Σ : gctx).
Implicit Types (b : bool).

Fixpoint ovalty_val (ω : expr) : expr :=
  match ω with
  | <{ 𝟙 }> => <{ () }>
  | <{ ~𝔹 }> => <{ [true] }>
  | <{ ω1 * ω2 }> => <{ (,(ovalty_val ω1), ,(ovalty_val ω2)) }>
  | <{ ω1 ~+ ω2 }> => <{ [inl<ω1 ~+ ω2> ,(ovalty_val ω1)] }>
  (* Bogus *)
  | _ => <{ () }>
  end.

Lemma ovalty_val_correct ω :
  otval ω -> ovalty (ovalty_val ω) ω.
Proof.
  induction ω; try case_label; try qauto inv: otval ctrs: ovalty.
Qed.

Reserved Notation "e '-->!' e'" (at level 40).

(** Expand evaluation context and re-order the rules. *)
Inductive step_alt : expr -> expr -> Prop :=
| SApp l τ e v :
    wval v ->
    <{ (\:{l}τ => e) v }> -->! <{ e^v }>
| SLet v e :
    wval v ->
    <{ let v in e }> -->! <{ e^v }>
| SCase b τ v e1 e2 :
    wval v ->
    <{ case inj@b<τ> v of e1 | e2 }> -->! <{ ite b (e1^v) (e2^v) }>
| SOCase b ω1 ω2 v e1 e2 :
    oval v ->
    otval ω1 -> otval ω2 ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
      <{ ~if [b] then (ite b (e1^v) (e1^,(ovalty_val ω1)))
                 else (ite b (e2^,(ovalty_val ω2)) (e2^v)) }>
| SFun x T e :
    Σ !! x = Some (DFun T e) ->
    <{ gvar x }> -->! <{ e }>
| SOInj b ω v :
    otval ω -> oval v ->
    <{ ~inj@b<ω> v }> -->! <{ [inj@b<ω> v] }>
| SIte b e1 e2 :
    <{ if b then e1 else e2 }> -->! <{ ite b e1 e2 }>
| SProj b v1 v2 :
    wval v1 -> wval v2 ->
    <{ π@b (v1, v2) }> -->! <{ ite b v1 v2 }>
| SFold X X' v :
    wval v ->
    <{ unfold<X> (fold <X'> v) }> -->! v
| SSec b :
    <{ s𝔹 b }> -->! <{ [b] }>
| SMux b v1 v2 :
    wval v1 -> wval v2 ->
    <{ mux [b] v1 v2 }> -->! <{ ite b v1 v2 }>
| STapeOIte b v1 v2 :
    woval v1 -> woval v2 ->
    <{ tape (~if [b] then v1 else v2) }> -->! <{ mux [b] (tape v1) (tape v2) }>
| STapePair v1 v2 :
    woval v1 -> woval v2 ->
    <{ tape (v1, v2) }> -->! <{ (tape v1, tape v2) }>
| STapeUnitV :
    <{ tape () }> -->! <{ () }>
| STapeBoxedLit b :
    <{ tape [b] }> -->! <{ [b] }>
| STapeBoxedInj b ω v :
    otval ω -> oval v ->
    <{ tape [inj@b<ω> v] }> -->! <{ [inj@b<ω> v] }>

| SOIteApp b v v1 v2 :
    wval v ->
    wval v1 -> wval v2 ->
    <{ (~if [b] then v1 else v2) v }> -->! <{ ~if [b] then v1 v else v2 v }>
| SOIteSec b v1 v2 :
    wval v1 -> wval v2 ->
    <{ s𝔹 (~if [b] then v1 else v2) }> -->! <{ ~if [b] then s𝔹 v1 else s𝔹 v2 }>
| SOIteIte b v1 v2 e1 e2 :
    wval v1 -> wval v2 ->
    <{ if (~if [b] then v1 else v2) then e1 else e2 }> -->!
      <{ ~if [b] then (if v1 then e1 else e2) else (if v2 then e1 else e2) }>
| SOIteProj b b' v1 v2 :
    wval v1 -> wval v2 ->
    <{ π@b' (~if [b] then v1 else v2) }> -->!
      <{ ~if [b] then π@b' v1 else π@b' v2 }>
| SOIteCase b v1 v2 e1 e2 :
    wval v1 -> wval v2 ->
    <{ case (~if [b] then v1 else v2) of e1 | e2 }> -->!
      <{ ~if [b] then (case v1 of e1 | e2) else (case v2 of e1 | e2) }>
| SOIteUnfold X b v1 v2 :
    wval v1 -> wval v2 ->
    <{ unfold<X> (~if [b] then v1 else v2) }> -->!
      <{ ~if [b] then unfold<X> v1 else unfold<X> v2 }>

| SCtxProd2 ω1 τ2 τ2' : otval ω1 -> τ2 -->! τ2' -> <{ ω1 * τ2 }> -->! <{ ω1 * τ2' }>
| SCtxProd1 τ1 τ1' τ2 : τ1 -->! τ1' -> <{ τ1 * τ2 }> -->! <{ τ1' * τ2 }>
| SCtxOSum2 ω1 τ2 τ2' : otval ω1 -> τ2 -->! τ2' -> <{ ω1 ~+ τ2 }> -->! <{ ω1 ~+ τ2' }>
| SCtxOSum1 τ1 τ1' τ2 : τ1 -->! τ1' -> <{ τ1 ~+ τ2 }> -->! <{ τ1' ~+ τ2 }>
| SCtxApp1 e1 e1' v2 : wval v2 -> e1 -->! e1' -> <{ e1 v2 }> -->! <{ e1' v2 }>
| SCtxApp2 e1 e2 e2' : e2 -->! e2' -> <{ e1 e2 }> -->! <{ e1 e2' }>
| SCtxTApp X e e' : e -->! e' -> <{ X@e }> -->! <{ X@e' }>
| STApp X τ e v :
    Σ !! X = Some (DOADT τ e) ->
    wval v ->
    <{ X@v }> -->! <{ e^v }>
| SCtxLet e1 e1' e2 : e1 -->! e1' -> <{ let e1 in e2 }> -->! <{ let e1' in e2 }>
| SCtxOIte3 v0 v1 e2 e2' : wval v0 -> wval v1 -> e2 -->! e2' -> <{ ~if v0 then v1 else e2 }> -->! <{ ~if v0 then v1 else e2' }>
| SCtxOIte2 v0 e1 e1' e2 : wval v0 -> e1 -->! e1' -> <{ ~if v0 then e1 else e2 }> -->! <{ ~if v0 then e1' else e2 }>
| SCtxOIte1 e0 e0' e1 e2 : e0 -->! e0' -> <{ ~if e0 then e1 else e2 }> -->! <{ ~if e0' then e1 else e2 }>
| SCtxOCase e0 e0' e1 e2 : e0 -->! e0' -> <{ ~case e0 of e1 | e2 }> -->! <{ ~case e0' of e1 | e2 }>
| SCtxPair2 v1 e2 e2' : wval v1 -> e2 -->! e2' -> <{ (v1, e2) }> -->! <{ (v1, e2') }>
| SCtxPair1 e1 e1' e2 : e1 -->! e1' -> <{ (e1, e2) }> -->! <{ (e1', e2) }>
| SCtxInj b τ e e' : e -->! e' -> <{ inj@b<τ> e }> -->! <{ inj@b<τ> e' }>
| SCtxOInj2 b ω e e' : otval ω -> e -->! e' -> <{ ~inj@b<ω> e }> -->! <{ ~inj@b<ω> e' }>
| SCtxOInj1 b τ τ' e : τ -->! τ' -> <{ ~inj@b<τ> e }> -->! <{ ~inj@b<τ'> e }>
| SCtxFold X e e' : e -->! e' -> <{ fold<X> e }> -->! <{ fold<X> e' }>
| SCtxTape e e' : e -->! e' -> <{ tape e }> -->! <{ tape e' }>
| SCtxMux3 v0 v1 e2 e2' : wval v0 -> wval v1 -> e2 -->! e2' -> <{ mux v0 v1 e2 }> -->! <{ mux v0 v1 e2' }>
| SCtxMux2 v0 e1 e1' e2 : wval v0 -> e1 -->! e1' -> <{ mux v0 e1 e2 }> -->! <{ mux v0 e1' e2 }>
| SCtxMux1 e0 e0' e1 e2 : e0 -->! e0' -> <{ mux e0 e1 e2 }> -->! <{ mux e0' e1 e2 }>
| SCtxSec e e' : e -->! e' -> <{ s𝔹 e }> -->! <{ s𝔹 e' }>
| SCtxIte e0 e0' e1 e2 : e0 -->! e0' -> <{ if e0 then e1 else e2 }> -->! <{ if e0' then e1 else e2 }>
| SCtxProj b e e' : e -->! e' -> <{ π@b e }> -->! <{ π@b e' }>
| SCtxCase e0 e0' e1 e2 : e0 -->! e0' -> <{ case e0 of e1 | e2 }> -->! <{ case e0' of e1 | e2 }>
| SCtxUnfold X e e' : e -->! e' -> <{ unfold<X> e }> -->! <{ unfold<X> e' }>


where "e '-->!' e'" := (step_alt e e').

Ltac apply_SOIte :=
  refine (eq_ind _ _ _ _ _); [
    match goal with
    | |- _ ⊨ ?e -->! _ =>
      match e with
      | context E [<{ ~if ?b then ?v1 else ?v2 }>] =>
        let ℇ := constr:(fun t : expr =>
                           ltac:(let t := context E [t] in exact t)) in
        change e with (ℇ <{ ~if b then v1 else v2 }>)
      end
    end;
    eapply SOIte | reflexivity ]; eauto using lectx.

Ltac ctx_solver :=
  solve [eapply SCtx_intro; [ eauto
                            | higher_order_reflexivity
                            | higher_order_reflexivity
                            | eauto using ectx, lectx ]
        | apply_SOIte; eauto using lectx ].

Lemma step_alt_step e e' : e -->! e' -> Σ ⊨ e -->! e'.
Proof.
  induction 1; eauto using step; try ctx_solver.

  eauto using step, ovalty_val_correct.
Qed.

Lemma mstep_alt_mstep e e' : rtc step_alt e e' -> Σ ⊨ e -->* e'.
Proof.
  induction 1; qauto ctrs: rtc use: step_alt_step.
Qed.

End step.

(** * Alternative typing and kinding rules *)
Section typing_kinding_alt.

Context (Σ : gctx).
Implicit Types (x : atom) (L : aset).
#[local]
Coercion EFVar : atom >-> expr.

Import notations.

Arguments open /.

Notation "Γ '⊢' e ':{' l '}' τ" := (Σ; Γ ⊢ e :{l} τ)
                                     (at level 40,
                                      e custom oadt at level 99,
                                      τ custom oadt at level 99).
Notation "Γ '⊢' τ '::' κ" := (Σ; Γ ⊢ τ :: κ)
                               (at level 40,
                                τ custom oadt at level 99,
                                κ custom oadt at level 99).

Lemma KProd_alt Γ τ1 τ2 κ1 κ2 :
  Γ ⊢ τ1 :: κ1 ->
  Γ ⊢ τ2 :: κ2 ->
  Γ ⊢ τ1 * τ2 :: κ1 ⊔ κ2.
Proof.
  intros.
  econstructor;
    econstructor; eauto using join_ub_l, join_ub_r.
Qed.

Lemma KSum_alt Γ τ1 τ2 κ1 κ2 :
  Γ ⊢ τ1 :: κ1 ->
  Γ ⊢ τ2 :: κ2 ->
  Γ ⊢ τ1 + τ2 :: (κ1 ⊔ κ2 ⊔ *@P).
Proof.
  intros.
  econstructor;
    econstructor; eauto using join_ub_l, join_ub_r.
Qed.

Lemma TProj1 Γ l e τ1 τ2 :
  Γ ⊢ e :{l} τ1 * τ2 ->
  Γ ⊢ π1 e :{l} τ1.
Proof.
  intros.
  relax_typing_type.
  econstructor; eauto.
  reflexivity.
Qed.

Lemma TProj2 Γ l e τ1 τ2 :
  Γ ⊢ e :{l} τ1 * τ2 ->
  Γ ⊢ π2 e :{l} τ2.
Proof.
  intros.
  relax_typing_type.
  econstructor; eauto.
  reflexivity.
Qed.

Lemma pared_equiv_ite1 τ1 τ2 :
  lc τ1 ->
  lc τ2 ->
  Σ ⊢ if true then τ1 else τ2 ≡ τ1.
Proof.
  repeat econstructor; eauto.
Qed.

Lemma pared_equiv_ite2 τ1 τ2 :
  lc τ1 ->
  lc τ2 ->
  Σ ⊢ if false then τ1 else τ2 ≡ τ2.
Proof.
  repeat econstructor; eauto.
Qed.

Lemma TIte_alt Γ l1 l2 l e0 e1 e2 τ1 τ2 :
  Γ ⊢ e0 :{⊥} 𝔹 ->
  Γ ⊢ e1 :{l1} τ1 ->
  Γ ⊢ e2 :{l2} τ2 ->
  Γ ⊢ τ1 :: *@O ->
  Γ ⊢ τ2 :: *@O ->
  l = l1 ⊔ l2 ->
  Γ ⊢ if e0 then e1 else e2 :{l} if e0 then τ1 else τ2.
Proof.
  intros.
  select! (_ ⊢ _ :: _) (fun H => dup_hyp H (fun H => apply kinding_lc in H)).
  eapply TConv with (τ' := <{ (if $0 then τ1 else τ2)^e0 }>);
    [ eapply TIte | .. ];
    eauto; simpl; rewrite ?open_lc by assumption;
      econstructor; eauto using kinding, typing.
  all : symmetry; eauto using pared_equiv_ite1, pared_equiv_ite2.
Qed.

(* These alternative rules can be more general, but it is more convenient to
have simplified versions. *)
Lemma TIte_alt_pi Γ l1 l2 l l' e0 e1 e2 τ1 τ2 τ κ:
  Γ ⊢ e0 :{⊥} 𝔹 ->
  Γ ⊢ e1 :{l1} Π:{l'}τ1, τ ->
  Γ ⊢ e2 :{l2} Π:{l'}τ2, τ ->
  Γ ⊢ τ1 :: *@O ->
  Γ ⊢ τ2 :: *@O ->
  Γ ⊢ τ :: κ ->
  l = l1 ⊔ l2 ->
  Γ ⊢ if e0 then e1 else e2 :{l} Π:{l'}if e0 then τ1 else τ2, τ.
Proof.
  intros.
  select! (_ ⊢ _ :: _) (fun H => dup_hyp H (fun H => apply kinding_lc in H)).
  eapply TConv with (τ' := <{ (Π:{l'}if $0 then τ1 else τ2, τ)^e0 }>);
    [ eapply TIte | .. ];
    eauto; simpl; rewrite ?open_lc by assumption; try reflexivity;
      repeat
        match goal with
        | |- _ ⊢ _ :{_} _ =>
          econstructor; simpl; eauto
        | |- _ ⊢ _ :: _ =>
          econstructor; simpl; simpl_cofin?;
            rewrite ?open_lc by assumption;
            eauto using kinding_weakening_insert
        end.

  all : symmetry; repeat (econstructor; simpl_cofin?);
    simpl; rewrite ?open_lc; eauto.
Qed.

Lemma open_lc_body_ e i s x :
  lc <{ e^x }> ->
  i <> 0 ->
  <{ {i~>s}e }> = e.
Proof.
  intros.
  rewrite (open_lc_) with (i:=0) (s:=x).
  reflexivity.
  rewrite open_lc.
  reflexivity.
  eauto.
  eauto.
Qed.

Lemma open_lc_body e s x :
  lc <{ e^x }> ->
  <{ {1~>s}e }> = e.
Proof.
  eauto using open_lc_body_.
Qed.

(* FIXME: the next few lemmas are very dirty. *)

Lemma pared_equiv_case1 τ1 τ2 τ e :
  lc e ->
  lc τ ->
  lc <{ τ1^e }> ->
  lc <{ τ2^e }> ->
  Σ ⊢ case inl<τ> e of τ1 | τ2 ≡ τ1^e.
Proof.
  intros.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl_cofin.
  econstructor.
  eapply open_respect_lc; eauto with lc.
  simpl_cofin.
  econstructor.
  eapply open_respect_lc; eauto with lc.
  econstructor; eauto with lc.
Qed.

Lemma pared_equiv_case2 τ1 τ2 τ e :
  lc e ->
  lc τ ->
  lc <{ τ1^e }> ->
  lc <{ τ2^e }> ->
  Σ ⊢ case inr<τ> e of τ1 | τ2 ≡ τ2^e.
Proof.
  intros.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl_cofin.
  econstructor.
  eapply open_respect_lc; eauto with lc.
  simpl_cofin.
  econstructor.
  eapply open_respect_lc; eauto with lc.
  econstructor; eauto with lc.
Qed.

Lemma TCase_alt_ Γ l1 l2 l e0 e1 e2 τ1 τ2 τ1' τ2' κ1 κ2 L1 L2 L3 L4 :
  Γ ⊢ e0 :{⊥} τ1' + τ2' ->
  (forall x, x ∉ L1 -> <[x:=(⊥, τ1')]>Γ ⊢ e1^x :{l1} τ1^x) ->
  (forall x, x ∉ L2 -> <[x:=(⊥, τ2')]>Γ ⊢ e2^x :{l2} τ2^x) ->
  (forall x, x ∉ L3 -> <[x:=(⊥, τ1')]>Γ ⊢ τ1^x :: *@O) ->
  (forall x, x ∉ L4 -> <[x:=(⊥, τ2')]>Γ ⊢ τ2^x :: *@O) ->
  Γ ⊢ τ1' :: κ1 ->
  Γ ⊢ τ2' :: κ2 ->
  l = l1 ⊔ l2 ->
  Γ ⊢ case e0 of e1 | e2 :{l} case e0 of τ1 | τ2.
Proof.
  intros.
  eapply TConv with (τ' := <{ (case $0 of τ1 | τ2)^e0 }>); eauto.
  eapply TCase; eauto.
  - dup_hyp H2 (fun H => block_hyp H).
    dup_hyp H3 (fun H => block_hyp H).
    simpl_cofin?; simpl.
    erewrite ?open_lc_body by eauto using kinding_lc.
    eapply TConv; eauto.
    symmetry. eapply pared_equiv_case1; eauto with lc.
    econstructor.
    econstructor.
    econstructor.
    simplify_map_eq. reflexivity.
    eauto using kinding_weakening_insert.
    eapply KSum_alt.
    eauto using kinding_weakening_insert.
    eauto using kinding_weakening_insert.

    unblock_hyps.
    simpl_cofin?; simpl.
    rewrite insert_commute by fast_set_solver!!.
    eapply kinding_weakening_insert.
    eauto. fast_set_solver!!.

    unblock_hyps.
    simpl_cofin?; simpl.
    rewrite insert_commute by fast_set_solver!!.
    eapply kinding_weakening_insert.
    eauto. fast_set_solver!!.

  - dup_hyp H2 (fun H => block_hyp H).
    dup_hyp H3 (fun H => block_hyp H).
    simpl_cofin?; simpl.
    erewrite ?open_lc_body by eauto using kinding_lc.
    eapply TConv; eauto.
    symmetry. eapply pared_equiv_case2; eauto with lc.
    econstructor.
    econstructor.
    econstructor.
    simplify_map_eq. reflexivity.
    eauto using kinding_weakening_insert.
    eapply KSum_alt.
    eauto using kinding_weakening_insert.
    eauto using kinding_weakening_insert.

    unblock_hyps.
    simpl_cofin?; simpl.
    rewrite insert_commute by fast_set_solver!!.
    eapply kinding_weakening_insert.
    eauto. fast_set_solver!!.

    unblock_hyps.
    simpl_cofin?; simpl.
    rewrite insert_commute by fast_set_solver!!.
    eapply kinding_weakening_insert.
    eauto. fast_set_solver!!.

  - simpl.
    econstructor; eauto.
    simpl_cofin.
    erewrite !open_lc_body by eauto using kinding_lc.
    eauto.
    simpl_cofin.
    erewrite !open_lc_body by eauto using kinding_lc.
    eauto.

  - simpl.
    simpl_cofin.
    erewrite !open_lc_body by eauto using kinding_lc.
    reflexivity.
  - econstructor; eauto.
Qed.

Lemma TCase_alt_pi_ Γ l1 l2 l l' e0 e1 e2 τ τ1 τ2 τ1' τ2' κ κ1 κ2 L1 L2 L3 L4 :
  Γ ⊢ e0 :{⊥} τ1' + τ2' ->
  (forall x, x ∉ L1 -> <[x:=(⊥, τ1')]>Γ ⊢ e1^x :{l1} Π:{l'}τ1^x, τ) ->
  (forall x, x ∉ L2 -> <[x:=(⊥, τ2')]>Γ ⊢ e2^x :{l2} Π:{l'}τ2^x, τ) ->
  (forall x, x ∉ L3 -> <[x:=(⊥, τ1')]>Γ ⊢ τ1^x :: *@O) ->
  (forall x, x ∉ L4 -> <[x:=(⊥, τ2')]>Γ ⊢ τ2^x :: *@O) ->
  Γ ⊢ τ1' :: κ1 ->
  Γ ⊢ τ2' :: κ2 ->
  Γ ⊢ τ :: κ ->
  l = l1 ⊔ l2 ->
  Γ ⊢ case e0 of e1 | e2 :{l} Π:{l'}case e0 of τ1 | τ2, τ.
Proof.
  intros.
  eapply TConv with (τ' := <{ (Π:{l'}case $0 of τ1 | τ2, τ)^e0 }>); eauto.
  eapply TCase; eauto.
  - dup_hyp H2 (fun H => block_hyp H).
    dup_hyp H3 (fun H => block_hyp H).
    simpl_cofin?; simpl.
    erewrite ?open_lc_body by eauto using kinding_lc.
    rewrite (open_lc τ) by eauto using kinding_lc.
    eapply TConv; eauto.
    symmetry.
    econstructor. econstructor.
    econstructor. econstructor; eauto with lc.
    simpl_cofin. econstructor; eauto using kinding_lc.
    simpl_cofin. econstructor; eauto using kinding_lc.
    eauto with lc.
    simpl_cofin. econstructor. simpl. rewrite open_lc by eauto using kinding_lc.
    eauto using kinding_lc.
    reflexivity.

    econstructor.
    simpl_cofin.
    simpl. rewrite open_lc by eauto using kinding_lc.
    eapply kinding_weakening_insert; eauto.
    eapply kinding_weakening_insert; eauto.
    fast_set_solver!!.
    econstructor.
    econstructor.
    econstructor.
    simplify_map_eq. reflexivity.
    eauto using kinding_weakening_insert.
    eapply KSum_alt.
    eauto using kinding_weakening_insert.
    eauto using kinding_weakening_insert.

    unblock_hyps.
    simpl_cofin?; simpl.
    rewrite insert_commute by fast_set_solver!!.
    eapply kinding_weakening_insert.
    eauto. fast_set_solver!!.

    unblock_hyps.
    simpl_cofin?; simpl.
    rewrite insert_commute by fast_set_solver!!.
    eapply kinding_weakening_insert.
    eauto. fast_set_solver!!.

  - dup_hyp H2 (fun H => block_hyp H).
    dup_hyp H3 (fun H => block_hyp H).
    simpl_cofin?; simpl.
    erewrite ?open_lc_body by eauto using kinding_lc.
    rewrite (open_lc τ) by eauto using kinding_lc.
    eapply TConv; eauto.
    symmetry.
    econstructor. econstructor.
    econstructor. econstructor; eauto with lc.
    simpl_cofin. econstructor; eauto using kinding_lc.
    simpl_cofin. econstructor; eauto using kinding_lc.
    eauto with lc.
    simpl_cofin. econstructor. simpl. rewrite open_lc by eauto using kinding_lc.
    eauto using kinding_lc.
    reflexivity.

    econstructor.
    simpl_cofin.
    simpl. rewrite open_lc by eauto using kinding_lc.
    eapply kinding_weakening_insert; eauto.
    eapply kinding_weakening_insert; eauto.
    fast_set_solver!!.
    econstructor.
    econstructor.
    econstructor.
    simplify_map_eq. reflexivity.
    eauto using kinding_weakening_insert.
    eapply KSum_alt.
    eauto using kinding_weakening_insert.
    eauto using kinding_weakening_insert.

    unblock_hyps.
    simpl_cofin?; simpl.
    rewrite insert_commute by fast_set_solver!!.
    eapply kinding_weakening_insert.
    eauto. fast_set_solver!!.

    unblock_hyps.
    simpl_cofin?; simpl.
    rewrite insert_commute by fast_set_solver!!.
    eapply kinding_weakening_insert.
    eauto. fast_set_solver!!.

  - simpl.
    econstructor; eauto.
    simpl_cofin. simpl.
    rewrite !(open_lc τ) by eauto using kinding_lc.
    eapply kinding_weakening_insert; eauto.
    econstructor; eauto.
    simpl_cofin.
    erewrite !open_lc_body by eauto using kinding_lc.
    eauto.
    simpl_cofin.
    erewrite !open_lc_body by eauto using kinding_lc.
    eauto.

  - simpl.
    simpl_cofin.
    erewrite !open_lc_body by eauto using kinding_lc.
    rewrite open_lc by eauto using kinding_lc.
    reflexivity.
  - econstructor; eauto.
    simpl_cofin.
    simpl. rewrite open_lc by eauto using kinding_lc.
    eapply kinding_weakening_insert; eauto.
    econstructor; eauto.
Qed.

Lemma TCase_alt Γ l1 l2 l e0 e1 e2 τ1 τ2 τ1' τ2' κ1 κ2 L1 L2 L3 L4 :
  Γ ⊢ e0 :{⊥} τ1' + τ2' ->
  (forall x, x ∉ L1 -> exists τ', <[x:=(⊥, τ1')]>Γ ⊢ e1^#x :{l1} τ' /\ lc τ' /\ τ1 = close x τ') ->
  (forall x, x ∉ L2 -> exists τ', <[x:=(⊥, τ2')]>Γ ⊢ e2^#x :{l2} τ' /\ lc τ' /\ τ2 = close x τ') ->
  (forall x, x ∉ L3 -> <[x:=(⊥, τ1')]>Γ ⊢ τ1^#x :: *@O) ->
  (forall x, x ∉ L4 -> <[x:=(⊥, τ2')]>Γ ⊢ τ2^#x :: *@O) ->
  Γ ⊢ τ1' :: κ1 ->
  Γ ⊢ τ2' :: κ2 ->
  l = l1 ⊔ l2 ->
  Γ ⊢ case e0 of e1 | e2 :{l} case e0 of τ1 | τ2.
Proof.
  intros.
  eapply TCase_alt_; eauto.
  simpl_cofin. simp_hyps. subst. rewrite open_close; eauto.
  simpl_cofin. simp_hyps. subst. rewrite open_close; eauto.
Qed.

Lemma TCase_alt_pi Γ l1 l2 l l' e0 e1 e2 τ τ1 τ2 τ1' τ2' κ κ1 κ2 L1 L2 L3 L4 :
  Γ ⊢ e0 :{⊥} τ1' + τ2' ->
  (forall x, x ∉ L1 -> exists τ', <[x:=(⊥, τ1')]>Γ ⊢ e1^x :{l1} Π:{l'}τ', τ /\ lc τ' /\ τ1 = close x τ') ->
  (forall x, x ∉ L2 -> exists τ', <[x:=(⊥, τ2')]>Γ ⊢ e2^x :{l2} Π:{l'}τ', τ /\ lc τ' /\ τ2 = close x τ') ->
  (forall x, x ∉ L3 -> <[x:=(⊥, τ1')]>Γ ⊢ τ1^x :: *@O) ->
  (forall x, x ∉ L4 -> <[x:=(⊥, τ2')]>Γ ⊢ τ2^x :: *@O) ->
  Γ ⊢ τ1' :: κ1 ->
  Γ ⊢ τ2' :: κ2 ->
  Γ ⊢ τ :: κ ->
  l = l1 ⊔ l2 ->
  Γ ⊢ case e0 of e1 | e2 :{l} Π:{l'}case e0 of τ1 | τ2, τ.
Proof.
  intros.
  eapply TCase_alt_pi_; eauto.
  simpl_cofin. simp_hyps. eauto. subst. rewrite open_close; eauto.
  simpl_cofin. simp_hyps. eauto. subst. rewrite open_close; eauto.
Qed.

Lemma pared_equiv_oadtapp X τ e1 e1' e2 :
  Σ !! X = Some (DOADT τ e1) ->
  lc e2 ->
  <{ e1^e2 }> = e1' ->
  Σ ⊢ X@e2 ≡ e1'.
Proof.
  intros. subst.
  repeat econstructor; eauto.
Qed.

Lemma pared_equiv_oadtapp_pi X l e1 e1' e2 τ τ' :
  Σ !! X = Some (DOADT τ e1) ->
  lc e2 ->
  lc τ' ->
  <{ e1^e2 }> = e1' ->
  Σ ⊢ Π:{l}X@e2, τ' ≡ Π:{l}e1', τ'.
Proof.
  intros. subst.
  repeat (econstructor; simpl_cofin?); eauto.
  simpl; rewrite open_lc; eauto.
Qed.

End typing_kinding_alt.

(** * Axiomatized primitive integers *)

(** ** Extensions *)
Axiom EInt : bool -> expr.
Axiom EIntLe : bool -> expr -> expr -> expr.
Axiom EIntLit : int -> expr.
Axiom EBoxedIntLit : int -> expr.
Axiom EIntSec : expr -> expr.
Axiom EIntRet : expr -> expr.

(** ** Notations *)
Module int_notations.

Import notations.

Notation "'int{' l '}'" := (EInt l) (in custom oadt, l constr).
Notation "'int'" := (EInt low) (in custom oadt).
Notation "'~int'" := (EInt high) (in custom oadt).
Notation "a '<={' l '}' b" := (EIntLe l a b) (in custom oadt at level 1,
                                                 l constr,
                                           a custom oadt,
                                           b custom oadt,
                                           no associativity).
Notation "a '<=' b" := (EIntLe low a b) (in custom oadt at level 1,
                                           a custom oadt,
                                           b custom oadt,
                                           no associativity).
Notation "a '~<=' b" := (EIntLe high a b) (in custom oadt at level 1,
                                           a custom oadt,
                                           b custom oadt,
                                           no associativity).
Notation "'s_int' e" := (EIntSec e) (in custom oadt at level 1,
                                             e custom oadt at level 0).
Notation "'r_int' e" := (EIntRet e) (in custom oadt at level 1,
                                             e custom oadt at level 0).
Notation "'i(' a ')'" := (EIntLit a) (in custom oadt at level 0,
                                           a constr at level 0,
                                           format "'i(' a ')'").
Notation "'i[' a ']'" := (EBoxedIntLit a) (in custom oadt at level 0,
                                           a constr at level 0,
                                           format "'i[' a ]").
Notation "'r𝔹' e" := <{ ~if e then true else false }> (in custom oadt at level 1,
                                                          e custom oadt at level 0).

End int_notations.

Import int_notations.

Section int_axioms.

Context (Σ : gctx).

Import Int63.

(** ** Semantics *)
Notation "e '-->!' e'" := (step_alt Σ e e') (at level 40).

Axiom SCtxIntLe1 : forall e1 e1' e2, e1 -->! e1' -> <{ e1 <= e2 }> -->! <{ e1' <= e2 }>.
Axiom SCtxIntLe2 : forall e1 e2 e2', wval e1 -> e2 -->! e2' -> <{ e1 <= e2 }> -->! <{ e1 <= e2' }>.
Axiom SIntLe : forall m n, <{ i(m) <= i(n) }> -->! <{ lit (leb m n) }>.
Axiom SOIntLe : forall m n, <{ i[m] <= i[n] }> -->! <{ [leb m n] }>.
Axiom SCtxIntSec : forall e e', e -->! e' -> <{ s_int e }> -->! <{ s_int e' }>.
Axiom SCtxIntRet : forall e e', e -->! e' -> <{ r_int e }> -->! <{ r_int e' }>.
Axiom SIntSec : forall m, <{ s_int i(m) }> -->! <{ i[m] }>.
Axiom SIntSecRet : forall m, <{ s_int (r_int i[m]) }> -->! <{ i[m] }>.
Axiom SIntLeOIte1 : forall b v1 v2 e2,
    wval v1 -> wval v2 -> wval e2 ->
    <{ (~if [b] then v1 else v2) <= e2 }> -->!
      <{ ~if [b] then (v1 <= e2) else (v2 <= e2) }>.
Axiom SIntLeOIte2 : forall b v1 v2 m,
    wval v1 -> wval v2 ->
    <{ i(m) <= (~if [b] then v1 else v2) }> -->!
      <{ ~if [b] then (i(m) <= v2) else (i(m) <= v2) }>.
Axiom SIntRetLe1 : forall m n, <{ r_int i[m] <= r_int i[n] }> -->! <{ r𝔹 ([leb m n]) }>.
Axiom SIntRetLe2 : forall m n, <{ r_int i[m] <= i(n) }> -->! <{ r𝔹 (i[m] ~<= i[n]) }>.
Axiom SIntRetLe3 : forall m n, <{ i(m) <= r_int i[n] }> -->! <{ r𝔹 (i[m] ~<= i[n]) }>.
Axiom STapeOInt : forall m, <{ tape i[m] }> -->! <{ i[m] }>.

(** ** Typing rules *)
Notation "Γ '⊢' e ':{' l '}' τ" := (Σ; Γ ⊢ e :{l} τ)
                                     (at level 40,
                                      e custom oadt at level 99,
                                      τ custom oadt at level 99).
Notation "Γ '⊢' τ '::' κ" := (Σ; Γ ⊢ τ :: κ)
                               (at level 40,
                                τ custom oadt at level 99,
                                κ custom oadt at level 99).

Axiom KInt : forall Γ, Γ ⊢ int :: *@P.
Axiom KOInt : forall Γ, Γ ⊢ ~int :: *@O.
Axiom TIntLe : forall Γ l1 l2 l a b,
    Γ ⊢ a :{l1} int ->
    Γ ⊢ b :{l2} int ->
    l = l1 ⊔ l2 ->
    Γ ⊢ a <= b :{l} 𝔹.
Axiom TOIntLe : forall Γ a b,
    Γ ⊢ a :{⊥} ~int ->
    Γ ⊢ b :{⊥} ~int ->
    Γ ⊢ a ~<= b :{⊥} ~𝔹.
Axiom TIntSec : forall Γ l a,
    Γ ⊢ a :{l} int ->
    Γ ⊢ s_int a :{l} ~int.
Axiom TIntRet : forall Γ a,
    Γ ⊢ a :{⊥} ~int ->
    Γ ⊢ r_int a :{⊤} int.

(** ** Values *)
Axiom VIntLit : forall n, val <{ i(n) }>.
Axiom OVOIntLit : forall n, oval <{ i[n] }>.
Lemma WIntLit : forall n, wval <{ i(n) }>.
Proof.
  eauto using VIntLit, val_wval.
Qed.
Lemma WOIntLit : forall n, wval <{ i[n] }>.
Proof.
  eauto using OVOIntLit, oval_val, val_wval.
Qed.
Lemma OWOIntLit : forall n, woval <{ i[n] }>.
Proof.
  eauto using OVOIntLit, oval_woval.
Qed.
Axiom OVOInt : otval <{ ~int }>.
Axiom OTOInt : forall m, ovalty <{ i[m] }> <{ ~int }>.
Axiom WIntRet : forall m, wval <{ r_int i[m] }>.

Axiom ovalty_val_oint : ovalty_val <{ ~int }> = <{ i[0] }>.

(** ** Local closure *)
Axiom lc_int : forall l, lc <{ int{l} }>.

(** ** Opening *)
Axiom open_int : forall k s l, <{ {k~>s}int{l} }> = <{ int{l} }>.
Axiom open_intle : forall k s l e1 e2, <{ {k~>s}(e1 <={l} e2) }> = <{ ({k~>s}e1) <={l} ({k~>s}e2) }>.
Axiom open_intsec : forall k s e, <{ {k~>s}(s_int e) }> = <{ s_int ({k~>s}e) }>.
Axiom open_intret : forall k s e, <{ {k~>s}(r_int e) }> = <{ r_int ({k~>s}e) }>.
Axiom open_lit : forall k s n, <{ {k~>s}(i(n)) }> = <{ i(n) }>.
Axiom open_boxedlit : forall k s n, <{ {k~>s}(i[n]) }> = <{ i[n] }>.

(** ** Closing *)
Axiom close_int : forall i x l, close_ i x <{ int{l} }> = <{ int{l} }>.

End int_axioms.

(** * Alternative global context typing *)

(** Global context typing through definition list. *)
Lemma gdefs_typing Ds :
  NoDup Ds.*1 ->
  gctx_typing (list_to_map Ds) <-> Forall (fun KD => (list_to_map Ds) ⊢₁ (KD.2)) Ds.
Proof.
  intros. subst.
  unfold gctx_typing.
  rewrite map_Forall_to_list.
  rewrite map_to_list_to_map; eauto.
  apply Forall_iff.
  intros [].
  reflexivity.
Qed.

Lemma gctx_gdefs_typing Ds Σ :
  Σ = list_to_map Ds ->
  NoDup Ds.*1 ->
  Forall (fun KD => Σ ⊢₁ (KD.2)) Ds ->
  gctx_typing Σ.
Proof.
  hauto use: gdefs_typing.
Qed.

(** * Tactics *)
Ltac kinding_intro :=
  match goal with
  | |- _; _ ⊢ int :: _ => eapply KInt
  | |- _; _ ⊢ ~int :: _ => eapply KOInt
  | |- _; _ ⊢ gvar _ :: _ => eapply KVarADT
  | |- _; _ ⊢ 𝟙 :: _ => eapply KUnit
  | |- _; _ ⊢ 𝔹{_} :: _ => eapply KBool
  | |- _; _ ⊢ Π:{_}_, _ :: _ => eapply KPi
  | |- _; _ ⊢ _@_ :: _ => eapply KApp
  | |- _; _ ⊢ _ * _ :: _ => eapply KProd_alt
  | |- _; _ ⊢ _ + _ :: _ => eapply KSum_alt
  | |- _; _ ⊢ _ ~+ _ :: _ => eapply KOSum
  | |- _; _ ⊢ if _ then _ else _ :: _ => eapply KIte
  | |- _; _ ⊢ case _ of _ | _ :: _ => eapply KCase
  | |- _; _ ⊢ let _ in _ :: _ => eapply KLet_intro
  | |- _; _ ⊢ _ :: ?κ => assert_fails (is_evar κ); eapply KSub
  end.

Ltac typing_intro :=
  match goal with
  | |- _; _ ⊢ _ <= _ : _ => eapply TIntLe
  | |- _; _ ⊢ _ ~<= _ : _ => eapply TOIntLe
  | |- _; _ ⊢ s_int _ : _ => eapply TIntSec
  | |- _; _ ⊢ r_int _ : _ => eapply TIntRet
  | |- _; _ ⊢ fvar _ : _ => eapply TFVar
  | |- _; _ ⊢ gvar _ : _ => eapply TGVar
  | |- _; _ ⊢ \:{_}_ => _ : _ => eapply TAbs
  | |- _; _ ⊢ let _ in _ : _ => eapply TLet
  | |- _; _ ⊢ _ _ : _ => eapply TApp
  | |- _; _ ⊢ () : _ => eapply TUnit
  | |- _; _ ⊢ lit _ : _ => eapply TLit
  | |- _; _ ⊢ s𝔹 _ : _ => eapply TSec
  | |- _; _ ⊢ (_, _) : _ => eapply TPair
  | |- _; _ ⊢ ~if _ then _ else _ : _ => eapply TOIte
  | |- _; _ ⊢ π1 _ : _ => eapply TProj1
  | |- _; _ ⊢ π2 _ : _ => eapply TProj2
  | |- _; _ ⊢ inj@_<_> _ : _ => eapply TInj
  | |- _; _ ⊢ ~inj@_<_> _ : _ => eapply TOInj
  | |- _; _ ⊢ ~case _ of _ | _ : _ => eapply TOCase
  | |- _; _ ⊢ fold<_> _ : _ => eapply TFold
  | |- _; _ ⊢ unfold<_> _ : _ => eapply TUnfold
  (* | H : _; _ ⊢ ?e :{⊥} _ |- _; _ ⊢ if ?e then _ else _ : _ => eapply TIte *)
  | |- _; _ ⊢ if _ then _ else _ : _ => eapply TIteNoDep
  (* | H : _; _ ⊢ ?e :{⊥} _ |- _; _ ⊢ case ?e of _ | _ : _ => eapply TCase *)
  | |- _; _ ⊢ case _ of _ | _ : _ => eapply TCaseNoDep
  | |- _; _ ⊢ tape _ : _ => eapply TTape
  | |- _; _ ⊢ mux _ _ _ : _ => eapply TMux
  | |- _; _ ⊢ [_] : _ => eapply TBoxedLit
  | |- _; _ ⊢ [inj@_<_> _] : _ => eapply TBoxedInj
  | |- _; _ ⊢ _ : ?τ => assert_fails (is_evar τ); eapply TConv
  end.

Ltac lookup_solver :=
  solve [ reflexivity
        | repeat select (_ ∉ {[_]}) (fun H => rewrite not_elem_of_singleton in H);
          simplify_map_eq; reflexivity ].

Ltac extract e := let e := eval unfold projT1, e in (projT1 e) in exact e.

Hint Rewrite open_int open_intle open_intsec open_intret open_lit open_boxedlit
  : open.

Ltac simpl_open :=
  unfold open; fold open_; simpl open_;
  (* rewrite ?open_int, ?open_intle, ?open_intsec, ?open_intret, ?open_lit, ?open_boxedlit. *)
  autorewrite with open.

Ltac simpl_ovalty :=
  simpl ovalty_val;
  rewrite ?ovalty_val_oint.

Ltac step_tac :=
  (eapply STapeOInt ||
   econstructor ||
   ((eapply WIntLit || eapply WOIntLit || eapply WIntRet ||
     eapply OVOInt || eapply OVOIntLit || eapply OWOIntLit ||
     eapply OTOInt ||
     eapply SOIntLe ||
     eapply SIntRetLe1 || eapply SIntRetLe2 || eapply SIntRetLe3 ||
     eapply SIntLe || (eapply SCtxIntLe2 + eapply SCtxIntLe1) ||
     eapply SIntSec || eapply SIntSecRet || eapply SCtxIntSec ||
     eapply SIntLeOIte1 || eapply SIntLeOIte2 ||
     eapply SCtxIntRet))).

Ltac mstep_tac :=
  simpl_ovalty; simpl_open;
  eapply Relation_Operators.rt1n_trans;
  [ do 40 step_tac | .. ].

Ltac typing_tac :=
  simpl_open;
  match goal with
  | |- _; _ ⊢ if _ then _ else _ : Π:{_}_ _, ?τ' =>
    eapply TConv; [ eapply TIte_alt_pi with (τ := τ') | .. ]
  | |- _; _ ⊢ if _ then _ else _ : _ _ =>
    eapply TConv; [ eapply TIte_alt | .. ]
  | |- _; _ ⊢ case _ of _ | _ : Π:{_}_ _, ?τ' =>
    eapply TConv; [ eapply TCase_alt_pi with (τ := τ') | .. ]
  | |- _; _ ⊢ case _ of _ | _ : _ _ =>
    eapply TConv; [ eapply TCase_alt | .. ]
  | |- _; _ ⊢ _ : _ => typing_intro
  | |- _; _ ⊢ _ :: _ => kinding_intro
  | |- _ ⊢₁ _ => econstructor
  | |- _ !! _ = _ => lookup_solver
  | |- _ ⊑ _ => reflexivity
  | |- _ = _ => reflexivity
  | |- _ ⊢ _ ≡ _ => reflexivity
  | |- _ ⊢ _ ≡ Π:{_}_ _, _ => symmetry
  | |- _ ⊢ Π:{_}_ _, _ ≡ _ => eapply pared_equiv_oadtapp_pi
  | |- _ ⊢ _ ≡ _ _ => symmetry
  | |- _ ⊢ _ _ ≡ _ => eapply pared_equiv_oadtapp
  | |- forall _, _ ∉ _ -> _ => simpl_cofin || simpl_cofin (∅ : aset)
  | |- lc _ => solve [ repeat econstructor; eauto using lc_int | eauto 10 with lc ]
  | |- exists _, _ => repeat esplit
  | |- _ = close _ _ =>
    unfold close; simpl close_;
    rewrite ?decide_True by auto; rewrite ?close_int; reflexivity
  end.
