From oadt.lang_oadt Require Import base syntax.
Import syntax.notations.

Implicit Types (b : bool).

(** * Definitions *)

(** ** OADT value typing *)
(** [ovalty v ω] means [v] is an oblivious value of oblivious type value [ω].
This is essentially a subset of [typing], but we have it so that the dynamic
semantics does not depend on typing. *)
Inductive ovalty : expr -> expr -> Prop :=
| OTUnit : ovalty <{ () }> <{ 𝟙 }>
| OTOBool b : ovalty <{ [b] }> <{ ~𝔹 }>
| OTProd v1 v2 ω1 ω2 :
  ovalty v1 ω1 -> ovalty v2 ω2 ->
  ovalty <{ ~(v1, v2) }> <{ ω1 ~* ω2 }>
| OTOSum b v ω1 ω2 :
  ovalty v <{ ite b ω1 ω2 }> ->
  (* Make sure the unused oblivious type is a value. *)
  otval <{ ite b ω2 ω1 }> ->
  ovalty <{ [inj@b<ω1 ~+ ω2> v] }> <{ ω1 ~+ ω2 }>
.

(** ** Evaluation context (ℇ) *)
(* This style is inspired by Iron Lambda. Maybe I should try other encoding
style later. This one can be quite annoying for proof automation. *)
(** We define evaluation context [ℇ] as the hole-filling function. [ℇ e] fills
the hole in [ℇ] with [e]. [ectx ℇ] asserts that [ℇ] is a well-formed
context. *)
Variant ectx : (expr -> expr) -> Prop :=
| CtxProd1 τ2 : ectx (fun τ1 => <{ τ1 ~* τ2 }>)
| CtxProd2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 ~* τ2 }>)
| CtxOSum1 τ2 : ectx (fun τ1 => <{ τ1 ~+ τ2 }>)
| CtxOSum2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 ~+ τ2 }>)
| CtxApp1 e2 : ectx (fun e1 => <{ e1 e2 }>)
| CtxApp2 v1 : val v1 -> ectx (fun e2 => <{ v1 e2 }>)
| CtxTApp X : ectx (fun e => <{ X@e }>)
| CtxLet e2 : ectx (fun e1 => <{ let e1 in e2 }>)
| CtxSec : ectx (fun e => <{ s𝔹 e }>)
| CtxIte e1 e2 : ectx (fun e0 => <{ if e0 then e1 else e2 }>)
| CtxPair1 l e2 : ectx (fun e1 => <{ (e1, e2){l} }>)
| CtxPair2 l v1 : val v1 -> ectx (fun e2 => <{ (v1, e2){l} }>)
| CtxProj l b : ectx (fun e => <{ π{l}@b e }>)
| CtxPsiPair1 e2 : ectx (fun e1 => <{ #(e1, e2) }>)
| CtxPsiPair2 v1 : val v1 -> ectx (fun e2 => <{ #(v1, e2) }>)
| CtxPsiProj b : ectx (fun e => <{ #π@b e }>)
| CtxInj b τ : ectx (fun e => <{ inj@b<τ> e }>)
| CtxOInj1 b e : ectx (fun τ => <{ ~inj@b<τ> e }>)
| CtxOInj2 b ω : otval ω -> ectx (fun e => <{ ~inj@b<ω> e }>)
| CtxCase e1 e2: ectx (fun e0 => <{ case e0 of e1 | e2 }>)
| CtxOCase e1 e2: ectx (fun e0 => <{ ~case e0 of e1 | e2 }>)
| CtxFold X : ectx (fun e => <{ fold<X> e }>)
| CtxUnfold X : ectx (fun e => <{ unfold<X> e }>)
| CtxMux1 e1 e2 : ectx (fun e0 => <{ mux e0 e1 e2 }>)
| CtxMux2 v0 e2 : val v0 -> ectx (fun e1 => <{ mux v0 e1 e2 }>)
| CtxMux3 v0 v1 : val v0 -> val v1 -> ectx (fun e2 => <{ mux v0 v1 e2 }>)
.

(** ** Small-step relation *)
Section step.

Context (Σ : gctx).

Reserved Notation "e '-->!' e'" (at level 40).

Inductive step : expr -> expr -> Prop :=
| SApp τ e v :
  val v ->
  <{ (\:τ => e) v }> -->! <{ e^v }>
| STApp X τ' τ v :
  val v ->
  Σ !! X = Some (DOADT τ' τ) ->
  <{ X@v }> -->! <{ τ^v }>
| SFun x T e :
  Σ !! x = Some (DFun T e) ->
  <{ gvar x }> -->! <{ e }>
| SLet v e :
  val v ->
  <{ let v in e }> -->! <{ e^v }>
| SSec b :
  <{ s𝔹 b }> -->! <{ [b] }>
| SIte b e1 e2 :
  <{ if b then e1 else e2 }> -->! <{ ite b e1 e2 }>
| SProj l b v1 v2 :
  val v1 -> val v2 ->
  <{ π{l}@b (v1, v2){l} }> -->! <{ ite b v1 v2 }>
| SPsiProj b v1 v2 :
  val v1 -> val v2 ->
  <{ #π@b #(v1, v2) }> -->! <{ ite b v1 v2 }>
| SOInj b ω v :
  otval ω -> oval v ->
  <{ ~inj@b<ω> v }> -->! <{ [inj@b<ω> v] }>
| SCase b τ v e1 e2 :
  val v ->
  <{ case inj@b<τ> v of e1 | e2 }> -->! <{ ite b (e1^v) (e2^v) }>
(* One of the most interesting rules. *)
| SOCase b ω1 ω2 v e1 e2 v1 v2 :
  oval v ->
  ovalty v1 ω1 -> ovalty v2 ω2 ->
  <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
  <{ mux [b] (ite b (e1^v) (e1^v1)) (ite b (e2^v2) (e2^v)) }>
| SUnfold X X' v :
  val v ->
  <{ unfold<X> (fold <X'> v) }> -->! v
| SMux b v1 v2 :
  val v1 -> val v2 ->
  <{ mux [b] v1 v2 }> -->! <{ ite b v1 v2 }>
(* Step under evaluation context *)
| SCtx ℇ e e' :
  ectx ℇ ->
  e -->! e' ->
  ℇ e -->! ℇ e'

where "e '-->!' e'" := (step e e').

End step.

(** * Notations *)
Module notations.

Notation "Σ '⊨' e '-->!' e'" := (step Σ e e') (at level 40,
                                                e custom oadt at level 99,
                                                e' custom oadt at level 99).

Notation "Σ '⊨' e '-->*' e'" := (rtc (step Σ) e e')
                                  (at level 40,
                                   e custom oadt at level 99,
                                   e' custom oadt at level 99).

Notation "Σ '⊨' e '-->{' n '}' e'" := (nsteps (step Σ) n e e')
                                        (at level 40,
                                         e custom oadt at level 99,
                                         n constr at level 99,
                                         e' custom oadt at level 99,
                                         format "Σ  '⊨'  e  '-->{' n '}'  e'").

Notation "e '-->!' e'" := (step _ e e') (at level 40).

Notation "e '-->*' e'" := (rtc (step _) e e') (at level 40).

Notation "e '-->{' n '}' e'" := (nsteps (step _) n e e') (at level 40).

End notations.
