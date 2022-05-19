(** This file is basically the same as [demo_prelude] but for the extension of
primitive integers. *)
From Coq Require Export Int63.Int63.
From stdpp Require Export pretty.
From oadt Require Import prelude.
From oadt Require Export lang_oadt.base.
From oadt Require Export demo.int.

#[local]
Set Default Proof Using "Type".

Import syntax_notations.
Import semantics_notations.
Import typing_notations.

(** * Alternative typing and kinding rules *)

Section typing_kinding_alt.

Context (Σ : gctx).
Implicit Types (x : atom) (L : aset).
#[local]
Coercion EFVar : atom >-> expr.

Arguments open /.

Lemma KProd_alt Γ τ1 τ2 κ1 κ2 :
  Γ ⊢ τ1 :: κ1 ->
  Γ ⊢ τ2 :: κ2 ->
  Γ ⊢ τ1 * τ2 :: (κ1 ⊔ κ2 ⊔ *@P).
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
  eapply TConv with (τ' := <{ (if bvar 0 then τ1 else τ2)^e0 }>);
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
  eapply TConv with (τ' := <{ (Π:{l'}if bvar 0 then τ1 else τ2, τ)^e0 }>);
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

Lemma pared_equiv_case1 τ1 τ2 τ e :
  lc e ->
  lc τ ->
  body <{ τ1 }> ->
  body <{ τ2 }> ->
  Σ ⊢ case inl<τ> e of τ1 | τ2 ≡ τ1^e.
Proof.
  unfold body. intros; simp_hyps.
  repeat (econstructor; eauto).
Qed.

Lemma pared_equiv_case2 τ1 τ2 τ e :
  lc e ->
  lc τ ->
  body <{ τ1 }> ->
  body <{ τ2 }> ->
  Σ ⊢ case inr<τ> e of τ1 | τ2 ≡ τ2^e.
Proof.
  unfold body. intros; simp_hyps.
  repeat (econstructor; eauto).
Qed.

Lemma open_body1 e s :
  body <{ e }> ->
  <{ {1~>s}e }> = e.
Proof.
  eauto using open_body.
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
  select! (forall x, _ -> _ ⊢ _ :: _) (fun H => dup_hyp H (fun H => apply kinding_body in H)).
  select! (_ ⊢ _ :: _) (fun H => dup_hyp H (fun H => apply kinding_lc in H)).
  eapply TConv with (τ' := <{ (case bvar 0 of τ1 | τ2)^e0 }>); eauto;
    [ eapply TCase; eauto | .. ]; simpl;
    try (goal_is (_ ⊢ _ :: _); econstructor; eauto);
    simpl_cofin*; simpl;
    rewrite ?open_body1 by assumption;
    try reflexivity; eauto;
    eapply TConv; eauto;
    try (goal_is (_ ⊢ _ ≡ _);
         symmetry; eapply pared_equiv_case1 || eapply pared_equiv_case2;
         eauto using lc);
    econstructor; simpl_cofin?;
    repeat match goal with
           | |- _ ⊢ _ :{_} _ =>
             econstructor; eauto with simpl_map
           | |- _ ⊢ _ :: _ =>
             try rewrite insert_commute by fast_set_solver!!;
             eapply kinding_weakening_insert; eauto using KSum_alt;
             fast_set_solver!!
           end.
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
  select! (forall x, _ -> _ ⊢ _ :: _) (fun H => dup_hyp H (fun H => apply kinding_body in H)).
  select! (_ ⊢ _ :: _) (fun H => dup_hyp H (fun H => apply kinding_lc in H)).
  eapply TConv with (τ' := <{ (Π:{l'}case bvar 0 of τ1 | τ2, τ)^e0 }>); eauto;
    [ eapply TCase; eauto | .. ]; simpl;
    try (goal_is (_ ⊢ _ :: _); econstructor; eauto);
    simpl_cofin*; simpl;
    rewrite ?open_body1 by assumption;
    repeat
      match goal with
      | |- context [ <{ {_~>_}?τ }> ] =>
        is_var τ; rewrite (open_lc τ) by assumption
      end;
    try solve [ reflexivity
              | eauto using kinding_weakening_insert
              | econstructor; eauto ];
    eapply TConv; eauto;
    try (goal_is (_ ⊢ _ ≡ _);
         unfold body in *; simp_hyps;
         symmetry; repeat (econstructor; eauto);
           by rewrite open_lc_intro);
    (econstructor;
     [ simpl_cofin;
       rewrite open_lc_intro by assumption;
       repeat (eapply kinding_weakening_insert; eauto);
       fast_set_solver!! | ]);
    econstructor; simpl_cofin?;
    repeat match goal with
           | |- _ ⊢ _ ≡ _ =>
             unfold body in *; simp_hyps;
             symmetry; repeat (econstructor; eauto);
             by rewrite open_lc_intro
           | |- _ ⊢ _ :{_} _ =>
             econstructor; eauto with simpl_map
           | |- _ ⊢ _ :: _ =>
             try rewrite insert_commute by fast_set_solver!!;
             eapply kinding_weakening_insert; eauto using KSum_alt;
             fast_set_solver!!
           end.

  Unshelve.
  all: exact ∅.
Qed.

Lemma TCase_alt Γ l1 l2 l e0 e1 e2 τ1 τ2 τ1' τ2' κ1 κ2 L1 L2 L3 L4 :
  Γ ⊢ e0 :{⊥} τ1' + τ2' ->
  (forall x, x ∉ L1 -> exists τ', <[x:=(⊥, τ1')]>Γ ⊢ e1^x :{l1} τ' /\ lc τ' /\ τ1 = close x τ') ->
  (forall x, x ∉ L2 -> exists τ', <[x:=(⊥, τ2')]>Γ ⊢ e2^x :{l2} τ' /\ lc τ' /\ τ2 = close x τ') ->
  (forall x, x ∉ L3 -> <[x:=(⊥, τ1')]>Γ ⊢ τ1^x :: *@O) ->
  (forall x, x ∉ L4 -> <[x:=(⊥, τ2')]>Γ ⊢ τ2^x :: *@O) ->
  Γ ⊢ τ1' :: κ1 ->
  Γ ⊢ τ2' :: κ2 ->
  l = l1 ⊔ l2 ->
  Γ ⊢ case e0 of e1 | e2 :{l} case e0 of τ1 | τ2.
Proof.
  intros.
  eapply TCase_alt_; eauto;
    simpl_cofin; simp_hyps; subst; rewrite open_close; eauto.
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
  eapply TCase_alt_pi_; eauto;
    simpl_cofin; simp_hyps; subst; rewrite open_close; eauto.
Qed.

Lemma pared_equiv_tapp X τ e1 e1' e2 :
  Σ !! X = Some (DOADT τ e1) ->
  lc e2 ->
  <{ e1^e2 }> = e1' ->
  Σ ⊢ X@e2 ≡ e1'.
Proof.
  intros. subst.
  repeat econstructor; eauto.
Qed.

Lemma pared_equiv_tapp_pi X l e1 e1' e2 τ τ' :
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

(** * Alternative global context typing *)

(** Global context typing through definition list. *)
Lemma gdefs_typing Ds :
  NoDup Ds.*1 ->
  gctx_typing (list_to_map Ds) <-> Forall (fun KD => (list_to_map Ds) ⊢₁ (KD.2)) Ds.
Proof.
  intros. subst.
  unfold gctx_typing.
  setoid_rewrite map_Forall_to_list.
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

Ltac lookup_solver :=
  solve [ reflexivity
        | repeat select (_ ∉ {[_]}) (fun H => rewrite not_elem_of_singleton in H);
          simplify_map_eq; reflexivity ].

Ltac extract e := let e := eval unfold proj1_sig, e in (proj1_sig e) in exact e.

Ltac simpl_open :=
  unfold open; fold open_; simpl open_.

Ltac typing_tac :=
  simpl_open;
  match goal with
  | |- _; _ ⊢ if _ then _ else _ : Π:{_}_@_, ?τ' =>
    eapply TConv; [ eapply TIte_alt_pi with (τ := τ') | .. ]
  | |- _; _ ⊢ if _ then _ else _ : _@_ =>
    eapply TConv; [ eapply TIte_alt | .. ]
  | |- _; _ ⊢ case _ of _ | _ : Π:{_}_@_, ?τ' =>
    eapply TConv; [ eapply TCase_alt_pi with (τ := τ') | .. ]
  | |- _; _ ⊢ case _ of _ | _ : _@_ =>
    eapply TConv; [ eapply TCase_alt | .. ]
  | |- _; _ ⊢ if _ then _ else _ : _ => eapply TIteNoDep
  | |- _; _ ⊢ case _ of _ | _ : _ => eapply TCaseNoDep
  | |- _; ?Γ ⊢ fvar ?x :{?l} _ =>
      assert_fails is_evar l;
      match Γ with
      | context [ <[x:=(l, _)]> _ ] => econstructor
      | _ => eapply TConv
      end
  | |- _; _ ⊢ _ : _ => econstructor
  | |- _; _ ⊢ _ * _ :: _ => eapply KProd_alt
  | |- _; _ ⊢ _ + _ :: _ => eapply KSum_alt
  | |- _; _ ⊢ _ :: _ => econstructor
  | |- _ ⊢₁ _ => econstructor
  | |- _ !! _ = _ => lookup_solver
  | |- _ ⊑ _ => reflexivity
  | |- _ = _ => reflexivity
  | |- _ ⊢ _ ≡ _ => reflexivity
  | |- _ ⊢ _ ≡ Π:{_}_@_, _ => symmetry
  | |- _ ⊢ Π:{_}_@_, _ ≡ _ => eapply pared_equiv_tapp_pi
  | |- _ ⊢ _ ≡ _@_ => symmetry
  | |- _ ⊢ _@_ ≡ _ => eapply pared_equiv_tapp
  | |- forall _, _ ∉ _ -> _ => simpl_cofin || simpl_cofin (∅ : aset)
  | |- lc _ => solve [ repeat econstructor; eauto | eauto 10 with lc ]
  | |- exists _, _ => repeat esplit
  | |- _ = close _ _ =>
    unfold close; simpl close_;
    rewrite ?decide_True by auto; reflexivity
  end.

Ltac gctx_typing_solver :=
  eapply gctx_gdefs_typing; [ reflexivity | compute_done | ];
  eapply Forall_fold_right; repeat split;
  repeat typing_tac.

Tactic Notation "mstep_solver" "with" constr(k) :=
  repeat esplit;
  [ eapply mstep_sound with (n:=k);
    vm_compute; reflexivity
  | try compute_done ].

Import Decimal.
(** Use a predefined fuel. *)
Ltac mstep_solver := mstep_solver with (Nat.of_num_uint 10000%uint).


(** * Notations *)

Module notations.

Export syntax_notations.
Export semantics_notations.
Export typing_notations.

(** When we write a name in the demos, it means global variable. *)
Coercion EGVar : atom >-> expr.

(** Sometimes we want a more explicit notation. *)
Notation "'$' n" := (EBVar n) (in custom oadt at level 0,
                                  n constr at level 0,
                                  format "'$' n").
Notation "'#' x" := (EGVar x) (in custom oadt at level 0,
                                  x custom oadt at level 0,
                                  only parsing).
Notation "'gvar' x" := (EGVar x) (in custom oadt at level 0,
                                     x constr at level 0,
                                     only parsing).
Notation "'fvar' x" := (EFVar x) (in custom oadt at level 0,
                                      x constr at level 0).

(** Alternatives to π1 and π2. *)
Notation "e '.1'" := <{ π1 e }> (in custom oadt at level 1,
                                    left associativity,
                                    format "e '.1'").
Notation "e '.2'" := <{ π2 e }> (in custom oadt at level 1,
                                    left associativity,
                                    format "e '.2'").
Notation "e '.~1'" := <{ ~π1 e }> (in custom oadt at level 1,
                                      left associativity,
                                      format "e '.~1'").
Notation "e '.~2'" := <{ ~π2 e }> (in custom oadt at level 1,
                                      left associativity,
                                      format "e '.~2'").

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
