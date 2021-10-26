From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.

Import syntax.notations.

Implicit Types (b : bool).

(** * Definitions *)

(** ** OADT value typing *)
(** This corresponds to the auxiliary oblivious value typing relation in Fig. 10
in the paper. *)
(** [ovalty v ω] means [v] is an oblivious value of oblivious type value [ω].
This is essentially a subset of [typing], but we have it so that the dynamic
semantics does not depend on typing. *)
Inductive ovalty : expr -> expr -> Prop :=
| OTUnit : ovalty <{ () }> <{ 𝟙 }>
| OTOBool b : ovalty <{ [b] }> <{ ~𝔹 }>
| OTProd v1 v2 ω1 ω2 :
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    ovalty <{ (v1, v2) }> <{ ω1 * ω2 }>
| OTOSum b v ω1 ω2 :
    ovalty v <{ ite b ω1 ω2 }> ->
    (* Make sure the unused oblivious type is a value. *)
    otval <{ ite b ω2 ω1 }> ->
    ovalty <{ [inj@b<ω1 ~+ ω2> v] }> <{ ω1 ~+ ω2 }>
.

(** ** Evaluation context (ℇ) *)
(* This style is inspired by Iron Lambda. Maybe I should try other encoding
style later. This one can be quite annoying for proof automation. *)
(** This corresponds to ℇ in Fig. 10 in the paper. *)
(** We define evaluation context [ℇ] as the hole-filling function. [ℇ e] fills
the hole in [ℇ] with [e]. [ectx ℇ] asserts that [ℇ] is a well-formed
context.

NOTE: we reduce applications from right to left for some subtle reason. *)
Inductive ectx : (expr -> expr) -> Prop :=
| CtxProd1 τ2 : ectx (fun τ1 => <{ τ1 * τ2 }>)
| CtxProd2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 * τ2 }>)
| CtxOSum1 τ2 : ectx (fun τ1 => <{ τ1 ~+ τ2 }>)
| CtxOSum2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 ~+ τ2 }>)
| CtxApp1 e1 : ectx (fun e2 => <{ e1 e2 }>)
| CtxApp2 v2 : val v2 -> ectx (fun e1 => <{ e1 v2 }>)
| CtxLet e2 : ectx (fun e1 => <{ let e1 in e2 }>)
| CtxSec : ectx (fun e => <{ s𝔹 e }>)
| CtxIte e1 e2 : ectx (fun e0 => <{ if e0 then e1 else e2 }>)
| CtxMux1 e1 e2 : ectx (fun e0 => <{ ~if e0 then e1 else e2 }>)
| CtxMux2 v0 e2 : val v0 -> ectx (fun e1 => <{ ~if v0 then e1 else e2 }>)
| CtxMux3 v0 v1 : val v0 -> val v1 -> ectx (fun e2 => <{ ~if v0 then v1 else e2 }>)
| CtxPair1 e2 : ectx (fun e1 => <{ (e1, e2) }>)
| CtxPair2 v1 : val v1 -> ectx (fun e2 => <{ (v1, e2) }>)
| CtxProj b : ectx (fun e => <{ π@b e }>)
| CtxInj b τ : ectx (fun e => <{ inj@b<τ> e }>)
| CtxOInj1 b e : ectx (fun τ => <{ ~inj@b<τ> e }>)
| CtxOInj2 b ω : otval ω -> ectx (fun e => <{ ~inj@b<ω> e }>)
| CtxCase l e1 e2: ectx (fun e0 => <{ case{l} e0 of e1 | e2 }>)
| CtxFold X : ectx (fun e => <{ fold<X> e }>)
| CtxUnfold X : ectx (fun e => <{ unfold<X> e }>)
.

(** ** Small-step relation *)
Section step.

Context (Σ : gctx).

Reserved Notation "e '-->!' e'" (at level 40).

(** This corresponds to the step relation in Fig. 10 in the paper. *)
Inductive step : expr -> expr -> Prop :=
| SApp τ e v :
    val v ->
    <{ (\:τ => e) v }> -->! <{ e^v }>
| SLet v e :
    val v ->
    <{ let v in e }> -->! <{ e^v }>
| SIf b e1 e2 :
    <{ if b then e1 else e2 }> -->! <{ ite b e1 e2 }>
| SCase b τ v e1 e2 :
    val v ->
    <{ case inj@b<τ> v of e1 | e2 }> -->! <{ ite b (e1^v) (e2^v) }>
| SProj b v1 v2 :
    val v1 -> val v2 ->
    <{ π@b (v1, v2) }> -->! <{ ite b v1 v2 }>
| SUnfold X X' v :
    val v ->
    <{ unfold<X> (fold <X'> v) }> -->! v
| SFun x τ e :
    Σ !! x = Some (DFun τ e) ->
    <{ gvar x }> -->! <{ e }>
| SOADT X τ e v :
    val v ->
    Σ !! X = Some (DOADT τ e) ->
    <{ (gvar X) v }> -->! <{ e^v }>
| SSec b :
    <{ s𝔹 b }> -->! <{ [b] }>
| SOInj b ω v :
    otval ω -> oval v ->
    <{ ~inj@b<ω> v }> -->! <{ [inj@b<ω> v] }>
| SMux b v1 v2 :
    val v1 -> val v2 ->
    <{ ~if [b] then v1 else v2 }> -->! <{ ite b v1 v2 }>
(* One of the most interesting rules. *)
| SOCase b ω1 ω2 v e1 e2 v1 v2 :
    oval v ->
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
      <{ ~if [b] then (ite b (e1^v) (e1^v1)) else (ite b (e2^v2) (e2^v)) }>
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
                                                e custom oadt at level 0,
                                                e' custom oadt at level 0).

Notation "Σ '⊨' e '-->*' e'" := (rtc (step Σ) e e')
                                  (at level 40,
                                   e custom oadt at level 0,
                                   e' custom oadt at level 0).

Notation "Σ '⊨' e '-->{' n '}' e'" := (nsteps (step Σ) n e e')
                                        (at level 40,
                                         e custom oadt at level 0,
                                         n constr at level 0,
                                         e' custom oadt at level 0,
                                         format "Σ  '⊨'  e  '-->{' n '}'  e'").

End notations.
