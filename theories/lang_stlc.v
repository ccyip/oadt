From oadt Require Import prelude.

(** This file is a playground for me to experiment with name binding and
automation, through simply typed lambda calculus. This development is adapted
from _Software Foundations_. The name binding approach mostly follows the paper
_The Locally Nameless Representation_, and is inspired by the Coq development
_formalmetacoq_ by the same author. *)

Module stlc.

Section lang.

Context `{is_atom : Atom atom amap aset}.
Implicit Types (x : atom) (L : aset).

(** * Syntax *)
Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_fvar  : atom -> tm
  | tm_bvar  : nat -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ : t , y" :=
  (tm_abs t y) (in custom stlc at level 90,
                   t custom stlc at level 99,
                   y custom stlc at level 99).

Coercion tm_fvar : atom >-> tm.
Coercion tm_bvar : nat >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).

Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

(** * Examples *)

Definition idB :=
  <{ \:Bool, 0 }>.

Notation idBB :=
  <{\:Bool->Bool, 0}>.

Notation idBBBB :=
  <{\:((Bool->Bool)->(Bool->Bool)), 0}>.

Notation k := <{\:Bool, \:Bool, 1}>.

Notation notB := <{\:Bool, if 0 then false else true}>.

(** * Small-step semantics *)

(** Variable opening *)
Reserved Notation "'[' k '~>' s ']' t" (in custom stlc at level 20, k constr).
Fixpoint open_ (k : nat) (s : tm) (t : tm) : tm :=
  match t with
  | tm_bvar n =>
      if decide (k = n) then s else t
  | <{\:T, t1}> =>
    <{\:T, [S k~>s] t1}>
  | <{t1 t2}> =>
      <{([k~>s] t1) ([k~>s] t2)}>
  | <{if t1 then t2 else t3}> =>
      <{if ([k~>s] t1) then ([k~>s] t2) else ([k~>s] t3)}>
  | _ => t
  end
where "'[' k '~>' s ']' t" := (open_ k s t) (in custom stlc).

Definition open s t := open_ 0 s t.

Notation "t ^ s" := (open s t) (in custom stlc at level 20).

(** Values *)
Inductive value : tm -> Prop :=
  | v_abs : forall T2 t1,
      value <{\:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

(** Unfortunately the notation --> is used in the standard library. *)
Reserved Notation "t '-->!' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T2 t1 v2,
         value v2 ->
         <{(\:T2, t1) v2}> -->! <{ t1 ^ v2 }>
  | ST_App1 : forall t1 t1' t2,
         t1 -->! t1' ->
         <{t1 t2}> -->! <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 -->! t2' ->
         <{v1 t2}> -->! <{v1 t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> -->! t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> -->! t2
  | ST_If : forall t1 t1' t2 t3,
      t1 -->! t1' ->
      <{if t1 then t2 else t3}> -->! <{if t1' then t2 else t3}>

where "t '-->!' t'" := (step t t').

Notation multistep := (clos_refl_trans_1n _ step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** * Typing *)
Notation context := (amap ty).

Reserved Notation "Gamma '⊢' t '\in' T" (at level 101,
                                          t custom stlc, T custom stlc at level 0).
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma !! x = Some T1 ->
      Gamma ⊢ x \in T1
  | T_Abs : forall Gamma T1 T2 t1 L,
      (forall x, x ∉ L -> <[x:=T2]>Gamma ⊢ t1 ^ x \in T1) ->
      Gamma ⊢ \:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma ⊢ t1 \in (T2 -> T1) ->
      Gamma ⊢ t2 \in T2 ->
      Gamma ⊢ t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma ⊢ true \in Bool
  | T_False : forall Gamma,
       Gamma ⊢ false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma ⊢ t1 \in Bool ->
       Gamma ⊢ t2 \in T1 ->
       Gamma ⊢ t3 \in T1 ->
       Gamma ⊢ if t1 then t2 else t3 \in T1

where "Gamma '⊢' t '\in' T" := (has_type Gamma t T).


(** * Infrastructure *)

(** Locally closed *)
Inductive lc : tm -> Prop :=
  | lc_var x : lc (tm_fvar x)
  | lc_true : lc <{ true }>
  | lc_false : lc <{ false }>
  | lc_if t1 t2 t3 : lc t1 -> lc t2 -> lc t3 -> lc <{ if t1 then t2 else t3 }>
  | lc_app t1 t2 : lc t1 -> lc t2 -> lc <{ t1 t2 }>
  | lc_abs T t L : (forall x, x ∉ L -> lc <{ t ^ x }>) -> lc <{ \:T, t }>
.

(** Substitution *)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : atom) (s : tm) (t : tm) : tm :=
  match t with
  | tm_fvar y =>
      if decide (x = y) then s else t
  | <{\:T, t1}> =>
      <{\:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | _ => t
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(** Free variables *)
Fixpoint fv (t : tm) : aset :=
  match t with
  | tm_fvar x => {[x]}
  | <{\:T, t1}> => fv t1
  | <{t1 t2}> => fv t1 ∪ fv t2
  | <{if t1 then t2 else t3}> => fv t1 ∪ fv t2 ∪ fv t3
  | _ => ∅
  end.

Notation "x # t" := (x ∉ fv t) (at level 40).

Definition closed t := fv t = ∅.

Instance atom_stale : @Stale aset atom := singleton.
Arguments atom_stale /.

Instance tm_stale : Stale tm := fv.
Arguments tm_stale /.

Instance context_stale : Stale context := dom aset.
Arguments context_stale /.

Instance aset_stale : Stale aset := id.
Arguments aset_stale /.

Lemma open_lc_ : forall t s u i j,
  i <> j ->
  <{ [j~>u]([i~>s] t) }> = <{ [i~>s] t }> ->
  <{ [j~>u] t }> = t.
Proof.
  induction t; hauto.
Qed.

(* NOTE: reordering the assumptions of [open_lc_] actually helps [sauto] to
work. [sauto] seems to struggle on the [i <> j] subgoal, where [i] is an
existential variable. If it solves the other subgoal first, [i] is instantiated
with a concrete value, then [sauto] has no problem with that. However, [eauto]
works pretty well in this case. *)
Lemma open_lc : forall t s,
  lc t -> forall k, <{ [k~>s] t }> = t.
Proof.
  induction 1; try hauto.
  - (* tm_abs *)
    simpl_cofin.
    intros. simpl. f_equal.
    eauto using open_lc_.
Qed.

Lemma subst_fresh : forall t x s,
  x # t -> <{ [x:=s] t }> = t.
Proof.
  induction t; hauto simp+: set_unfold.
Qed.

Lemma subst_open : forall t x s v,
  lc s ->
  <{ [x:=s] (t ^ v) }> = <{ ([x:=s] t) ^ ([x:=s] v) }>.
Proof.
  intros t. unfold open. generalize 0.
  induction t; hauto use: open_lc.
Qed.

Lemma subst_open_comm : forall t x y s,
  x <> y ->
  lc s ->
  <{ [x:=s] (t ^ y) }> = <{ ([x:=s] t) ^ y }>.
Proof.
  qauto use: subst_open.
Qed.

(** We may prove this one using [subst_open] and [subst_fresh], but a direct
induction gives us a slightly stronger version (without the local closure
constraint). *)
Lemma subst_intro : forall t s x,
  x # t ->
  <{ t ^ s }> = <{ [x:=s] (t ^ x) }>.
Proof.
  intros t. unfold open. generalize 0.
  induction t; hauto simp+: set_unfold.
Qed.

(** Well-typed terms are locally closed. *)
Lemma has_type_lc : forall Gamma t T,
  Gamma ⊢ t \in T ->
  lc t.
Proof.
  induction 1; hauto ctrs: lc.
Qed.

(** * Metatheories *)

(** ** Progress *)
Theorem progress : forall t T,
  empty ⊢ t \in T ->
  value t \/ exists t', t -->! t'.
Proof.
  remember empty as Gamma.
  induction 1; hauto solve: simplify_map_eq
                     ctrs: value, step
                     inv: value, has_type.
Qed.

(** ** Preservation *)

Lemma weakening : forall Gamma Gamma' t T,
  Gamma ⊢ t \in T ->
  Gamma ⊆ Gamma' ->
  Gamma' ⊢ t \in T.
Proof.
  intros Gamma Gamma' t T Ht. revert Gamma'.
  induction Ht;
    hauto use: lookup_weaken, insert_mono ctrs: has_type.
Qed.

Lemma weakening_insert : forall Gamma t T x T',
  x ∉ dom aset Gamma ->
  Gamma ⊢ t \in T ->
  <[x:=T']>Gamma ⊢ t \in T.
Proof.
  eauto using weakening, insert_fresh_subseteq.
Qed.

Lemma subst_preversation : forall t Gamma x v T1 T2,
  <[x:=T1]>Gamma ⊢ t \in T2 ->
  Gamma ⊢ v \in T1 ->
  Gamma ⊢ <{ [x:=v] t }> \in T2.
Proof.
  intros t Gamma x v T1 T2 Ht.
  remember (<[x:=T1]>Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros; subst;
    try hauto simp+: simplify_map_eq ctrs: has_type.
  - (* T_Abs *)
    intros. simpl. econstructor.
    simpl_cofin.
    rewrite <- subst_open_comm
      by eauto using has_type_lc with set_solver.
    qauto simp: set_unfold use: insert_commute, weakening_insert.
Qed.

Theorem preservation : forall Gamma t t' T,
  Gamma ⊢ t \in T  ->
  t -->! t'  ->
  Gamma ⊢ t' \in T.
Proof.
  intros Gamma t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; sinvert HE; try qauto ctrs: has_type.
  - (* T_App *)
    sinvert HT1.
    simpl_cofin.
    erewrite subst_intro by eauto.
    eauto using subst_preversation.
Qed.

(** ** Soundness *)
Definition normal_form {X : Type}
           (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty ⊢ t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  induction 2; qauto unfold: normal_form, stuck use: progress, preservation.
Qed.

End lang.
End stlc.
