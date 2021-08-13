From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.

Import syntax.notations.

Implicit Types (b : bool).

(** * Definitions *)

(** ** Weak values *)
Inductive wval : expr -> Prop :=
| WUnitV : wval <{ () }>
| WLit b : wval <{ lit b }>
| WPair v1 v2 : wval v1 -> wval v2 -> wval <{ (v1, v2) }>
| WAbs l τ e : wval <{ \:{l}τ => e }>
| WInj b τ v : wval v -> wval <{ inj@b<τ> v }>
| WFold X v : wval v -> wval <{ fold<X> v }>
| WBoxedLit b : wval <{ [b] }>
| WBoxedInj b ω v : otval ω -> oval v -> wval <{ [inj@b<ω> v] }>
| WIte b v1 v2 :
    wval v1 -> wval v2 ->
    wval <{ ~if [b] then v1 else v2 }>
.

(** ** Weak oblivious values *)
Inductive woval : expr -> Prop :=
| OWUnitV : woval <{ () }>
| OWBoxedLit b : woval <{ [b] }>
| OWPair v1 v2 : woval v1 -> woval v2 -> woval <{ (v1, v2) }>
| OWBoxedInj b ω v : otval ω -> oval v -> woval <{ [inj@b<ω> v] }>
| OWIte b v1 v2 :
    woval v1 -> woval v2 ->
    woval <{ ~if [b] then v1 else v2 }>
.

(** ** OADT value typing *)
(** [ovalty v ω] means [v] is an oblivious value of oblivious type value [ω].
This is essentially a subset of [typing], but we have it so that the dynamic
semantics does not depend on typing. *)
Inductive ovalty : expr -> expr -> Prop :=
| OTUnitV : ovalty <{ () }> <{ 𝟙 }>
| OTOBool b : ovalty <{ [b] }> <{ ~𝔹 }>
| OTPair v1 v2 ω1 ω2 :
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
(** We define evaluation context [ℇ] as the hole-filling function. [ℇ e] fills
the hole in [ℇ] with [e]. [ectx ℇ] asserts that [ℇ] is a well-formed
context.

NOTE: we reduce applications from right to left for some subtle reason. *)

(** The evaluation context enclosing possibly leaking expressions. *)
Variant lectx : (expr -> expr) -> Prop :=
| CtxApp1 v2 : wval v2 -> lectx (fun e1 => <{ e1 v2 }>)
| CtxSec : lectx (fun e => <{ s𝔹 e }>)
| CtxIte e1 e2 : lectx (fun e0 => <{ if e0 then e1 else e2 }>)
| CtxProj b : lectx (fun e => <{ π@b e }>)
| CtxCase e1 e2: lectx (fun e0 => <{ case e0 of e1 | e2 }>)
| CtxUnfold X : lectx (fun e => <{ unfold<X> e }>)
.

(** The top-level evaluation context. *)
Variant ectx : (expr -> expr) -> Prop :=
| CtxProd1 τ2 : ectx (fun τ1 => <{ τ1 * τ2 }>)
| CtxProd2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 * τ2 }>)
| CtxOSum1 τ2 : ectx (fun τ1 => <{ τ1 ~+ τ2 }>)
| CtxOSum2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 ~+ τ2 }>)
| CtxApp2 e1 : ectx (fun e2 => <{ e1 e2 }>)
| CtxLet e2 : ectx (fun e1 => <{ let e1 in e2 }>)
| CtxOIte1 e1 e2 : ectx (fun e0 => <{ ~if e0 then e1 else e2 }>)
| CtxOIte2 v0 e2 : wval v0 -> ectx (fun e1 => <{ ~if v0 then e1 else e2 }>)
| CtxOIte3 v0 v1 : wval v0 -> wval v1 -> ectx (fun e2 => <{ ~if v0 then v1 else e2 }>)
| CtxOCase e1 e2: ectx (fun e0 => <{ ~case e0 of e1 | e2 }>)
| CtxPair1 e2 : ectx (fun e1 => <{ (e1, e2) }>)
| CtxPair2 v1 : wval v1 -> ectx (fun e2 => <{ (v1, e2) }>)
| CtxInj b τ : ectx (fun e => <{ inj@b<τ> e }>)
| CtxOInj1 b e : ectx (fun τ => <{ ~inj@b<τ> e }>)
| CtxOInj2 b ω : otval ω -> ectx (fun e => <{ ~inj@b<ω> e }>)
| CtxFold X : ectx (fun e => <{ fold<X> e }>)
| CtxTape : ectx (fun e => <{ tape e }>)
| CtxMux1 e1 e2 : ectx (fun e0 => <{ mux e0 e1 e2 }>)
| CtxMux2 v0 e2 : wval v0 -> ectx (fun e1 => <{ mux v0 e1 e2 }>)
| CtxMux3 v0 v1 : wval v0 -> wval v1 -> ectx (fun e2 => <{ mux v0 v1 e2 }>)
(* A [lectx] is also a [ectx]. *)
| CtxLeak ℇ : lectx ℇ -> ectx ℇ
.

(** ** Small-step relation *)
Section step.

Context (Σ : gctx).

Reserved Notation "e '-->!' e'" (at level 40).

Inductive step : expr -> expr -> Prop :=
| SApp l τ e v :
    wval v ->
    <{ (\:{l}τ => e) v }> -->! <{ e^v }>
| SLet v e :
    wval v ->
    <{ let v in e }> -->! <{ e^v }>
| SCase b τ v e1 e2 :
    wval v ->
    <{ case inj@b<τ> v of e1 | e2 }> -->! <{ ite b (e1^v) (e2^v) }>
(* One of the most interesting rules. *)
| SOCase b ω1 ω2 v e1 e2 v1 v2 :
    oval v ->
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
      <{ ~if [b] then (ite b (e1^v) (e1^v1)) else (ite b (e2^v2) (e2^v)) }>
| SAppOADT X τ e v :
    wval v ->
    Σ !! X = Some (DOADT τ e) ->
    <{ (gvar X) v }> -->! <{ e^v }>
| SAppFun x T e :
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
(* [tape v] is a no-op if [v] is an oblivious value (except for pair). Spell
out all the cases here for determinism and proof convenience. *)
| STapeUnitV :
    <{ tape () }> -->! <{ () }>
| STapeBoxedLit b :
    <{ tape [b] }> -->! <{ [b] }>
| STapeBoxedInj b ω v :
    otval ω -> oval v ->
    <{ tape [inj@b<ω> v] }> -->! <{ [inj@b<ω> v] }>
| SOIte b v1 v2 ℇ :
    lectx ℇ ->
    wval v1 -> wval v2 ->
    ℇ <{ ~if [b] then v1 else v2 }> -->! <{ ~if [b] then ,(ℇ v1) else ,(ℇ v2) }>
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

Notation "Σ '⊨' e '-->*' e'" := (clos_refl_trans_1n _ (step Σ) e e')
                                  (at level 40,
                                   e custom oadt at level 0,
                                   e' custom oadt at level 0).

Notation "Σ '⊨' e '-->{' n '}' e'" := (trans_ext _ (step Σ) e e' n)
                                        (at level 40,
                                         e custom oadt at level 0,
                                         n constr at level 0,
                                         e' custom oadt at level 0,
                                         format "Σ  '⊨'  e  '-->{' n '}'  e'").

End notations.
