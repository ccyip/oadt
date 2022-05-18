(** Some decision procedures and implementations. *)
From oadt.lang_oadt Require Import
     base syntax semantics infrastructure admissible values.
Import syntax.notations semantics.notations.

(** * Decision procedures *)
Section dec.

(** The use of [abstract] is quite important for performance when we run it
within Coq. *)
Ltac t :=
  solve [ repeat
            (try solve [ left; abstract (econstructor; eauto using oval)
                       | right; abstract (inversion 1; subst;
                                          try contradiction;
                                          repeat oval_inv) ];
             try match reverse goal with
                 | H : sumbool _ _ |- _ => destruct H
                 end) ].

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
  | H : context [ oval ?ω ] |- context [<{ [inj@_<(?ω)> _] }>] =>
    clear H; destruct (decide (otval ω)); try t
  end.
Defined.

#[global]
Instance wval_dec v : Decision (wval v).
Proof.
  hnf. induction v; try t; try case_label; try t.
  match goal with
  | H : context [ wval ?v] |- context [<{ ~if ?v then _ else _ }>] =>
      clear H; destruct v; try t
  end.
  all:
    match goal with
    | |- context [ wval ?e ] =>
        destruct (decide (oval e)); t
    end.
Defined.

#[global]
Instance woval_dec v : Decision (woval v).
Proof.
  hnf. induction v; try t; try case_label; try t.
  match goal with
  | H : context [ woval ?v] |- context [<{ ~if ?v then _ else _ }>] =>
      clear H; destruct v; try t
  end.
  all:
    match goal with
    | |- context [ woval ?e ] =>
        destruct (decide (oval e)); t
    end.
Defined.

#[global]
Instance val_dec v : Decision (val v).
Proof.
  hnf. induction v; try t; try case_label; try t.
  all:
    match goal with
    | |- context [ val ?e ] =>
        destruct (decide (oval e)); t
    end.
Defined.

End dec.


(** * A naive implementation of [step] *)

Section step.

(** ** Definitions *)

Context (Σ : gctx).

Fixpoint ovalty_ (ω : expr) : option expr :=
  match ω with
  | <{ 𝟙 }> => mret <{ () }>
  | <{ ~𝔹 }> => mret <{ [true] }>
  | <{ ω1 ~* ω2 }> => v1 <- ovalty_ ω1; v2 <- ovalty_ ω2; mret <{ ~(v1, v2) }>
  | <{ ω1 ~+ ω2 }> =>
      guard (otval ω2); v <- ovalty_ ω1; mret <{ [inl<ω1 ~+ ω2> v] }>
  | _ => None
  end.

Fixpoint step_ (e : expr) : option expr :=
  match e with
  | <{ e1 e2 }> =>
    if decide (wval e1)
    then if decide (wval e2)
         then match e1 with
              | <{ \:{_}_ => e }> => mret <{ e^e2 }>
              | <{ ~if [b] then v1 else v2 }> =>
                  mret <{ ~if [b] then v1 e2 else v2 e2 }>
              | _ => None
              end
         else e2' <- step_ e2; mret <{ e1 e2' }>
    else e1' <- step_ e1; mret <{ e1' e2 }>
  | <{ X@e }> =>
    if decide (wval e)
    then match Σ !! X with
         | Some (DOADT _ e') => mret <{ e'^e }>
         | _ => None
         end
    else e' <- step_ e; mret <{ X@e' }>
  | <{ let e1 in e2 }> =>
    if decide (wval e1)
    then mret <{ e2^e1 }>
    else e1' <- step_ e1; mret <{ let e1' in e2 }>
  | <{ gvar x }> =>
    match Σ !! x with
    | Some (DFun _ e) => mret e
    | _ => None
    end
  | <{ s𝔹 e }> =>
    if decide (wval e)
    then match e with
         | <{ lit b }> => mret <{ [b] }>
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then s𝔹 v1 else s𝔹 v2 }>
         | _ => None
         end
    else e' <- step_ e; mret <{ s𝔹 e' }>
  | <{ if e0 then e1 else e2 }> =>
    if decide (wval e0)
    then match e0 with
         | <{ lit b }> => mret <{ ite b e1 e2 }>
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then (if v1 then e1 else e2)
                           else (if v2 then e1 else e2) }>
         | _ => None
         end
    else e0' <- step_ e0; mret <{ if e0' then e1 else e2 }>
  | <{ τ1 ~* τ2 }> =>
    if decide (otval τ1)
    then τ2' <- step_ τ2; mret <{ τ1 ~* τ2' }>
    else τ1' <- step_ τ1; mret <{ τ1' ~* τ2 }>
  | <{ (e1, e2){l} }> =>
    if decide (wval e1)
    then e2' <- step_ e2; mret <{ (e1, e2'){l} }>
    else e1' <- step_ e1; mret <{ (e1', e2){l} }>
  | <{ π@b e }> =>
    if decide (wval e)
    then match e with
         | <{ (v1, v2) }> => mret <{ ite b v1 v2 }>
         | <{ ~if [b'] then v1 else v2 }> =>
          mret <{ ~if [b'] then π@b v1 else π@b v2 }>
         | _ => None
         end
    else e' <- step_ e; mret <{ π@b e' }>
  | <{ ~π@b e }> =>
    if decide (wval e)
    then match e with
         | <{ ~(v1, v2) }> => mret <{ ite b v1 v2 }>
         | _ => None
         end
    else e' <- step_ e; mret <{ ~π@b e' }>
  | <{ τ1 ~+ τ2 }> =>
    if decide (otval τ1)
    then τ2' <- step_ τ2; mret <{ τ1 ~+ τ2' }>
    else τ1' <- step_ τ1; mret <{ τ1' ~+ τ2 }>
  | <{ inj@b<τ> e }> => e' <- step_ e; mret <{ inj@b<τ> e' }>
  | <{ ~inj@b<τ> e }> =>
    if decide (otval τ)
    then if decide (oval e)
         then mret <{ [inj@b<τ> e] }>
         else e' <- step_ e; mret <{ ~inj@b<τ> e' }>
    else τ' <- step_ τ; mret <{ ~inj@b<τ'> e }>
  | <{ case e0 of e1 | e2 }> =>
    if decide (wval e0)
    then match e0 with
         | <{ inj@b<_> v }> => mret <{ ite b (e1^v) (e2^v) }>
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then (case v1 of e1 | e2) else (case v2 of e1 | e2) }>
         | _ => None
         end
    else e0' <- step_ e0; mret <{ case e0' of e1 | e2 }>
  | <{ ~case e0 of e1 | e2 }> =>
    if decide (wval e0)
    then match e0 with
         | <{ [inj@b<ω1 ~+ ω2> v] }> =>
           v1 <- ovalty_ ω1; v2 <- ovalty_ ω2;
           mret <{ ~if [b] then (ite b (e1^v) (e1^v1))
                           else (ite b (e2^v2) (e2^v)) }>
         | _ => None
         end
    else e0' <- step_ e0; mret <{ ~case e0' of e1 | e2 }>
  | <{ fold<X> e }> => e' <- step_ e; mret <{ fold<X> e' }>
  | <{ unfold<X> e }> =>
    if decide (wval e)
    then match e with
         | <{ fold <_> v }> => mret v
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then unfold<X> v1 else unfold<X> v2 }>
         | _ => None
         end
    else e' <- step_ e; mret <{ unfold<X> e' }>
  | <{ tape e }> =>
    if decide (woval e)
    then match e with
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ mux [b] (tape v1) (tape v2) }>
         | _ => mret e
         end
    else e' <- step_ e; mret <{ tape e' }>
  | <{ mux e0 e1 e2 }> =>
    if decide (wval e0)
    then if decide (wval e1)
         then if decide (wval e2)
              then match e0 with
                   | <{ [b] }> => mret <{ ite b e1 e2 }>
                   | _ => None
                   end
              else e2' <- step_ e2; mret <{ mux e0 e1 e2' }>
         else e1' <- step_ e1; mret <{ mux e0 e1' e2 }>
    else e0' <- step_ e0; mret <{ mux e0' e1 e2 }>
  | <{ ~if e0 then e1 else e2 }> =>
    if decide (wval e0)
    then if decide (wval e1)
         then e2' <- step_ e2; mret <{ ~if e0 then e1 else e2' }>
         else e1' <- step_ e1; mret <{ ~if e0 then e1' else e2 }>
    else e0' <- step_ e0; mret <{ ~if e0' then e1 else e2 }>
  | _ => None
  end.

Fixpoint mstep_ (n : nat) (e : expr) : expr :=
  match n with
  | 0 => e
  | S n =>
      match step_ e with
      | Some e' => mstep_ n e'
      | None => e
      end
  end.


(** ** Correctness *)

#[local]
Set Default Proof Using "Type".

Lemma ovalty_sound ω : forall e,
  ovalty_ ω = Some e ->
  ovalty e ω.
Proof.
  induction ω; simpl; intros; try case_label; simplify_eq; simplify_option_eq;
    eauto using ovalty.
Qed.

Lemma step_sound e : forall e',
  step_ e = Some e' ->
  e -->! e'.
Proof.
  induction e; intros ? H; simplify_eq; simpl in H;
    repeat case_decide;
    repeat
      match goal with
      | H : match ?e with _ => _ end = _ |- _ =>
          sdestruct e; simplify_eq
      end; try wval_inv; try woval_inv; try oval_inv;
    (* Remove induction hypotheses when they are not needed to avoid unnecessary
    subgoals from [simplify_option_eq]. *)
    repeat
      match goal with
      | IH : forall _, step_ ?e = _ -> _ -->! _ |- _ =>
          assert_fails is_var e; clear IH
      end;
    simplify_option_eq;
    try solve [ eauto using step, oval, oval_wval | solve_ctx ].

  eauto using step, ovalty_sound.
Qed.

Lemma mstep_sound n : forall e e',
  mstep_ n e = e' ->
  e -->* e'.
Proof.
  induction n; simpl; intros; subst; try reflexivity.
  case_split; try reflexivity.
  eapply rtc_l; eauto using step_sound.
Qed.

End step.
