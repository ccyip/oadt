From oadt Require Import prelude.
From oadt Require Import lang_oadt.syntax.

(** * Dynamic semantics *)

Module M (atom_sig : AtomSig).

Include syntax.M atom_sig.
Import syntax_notations.

Implicit Types (b : bool).

(** ** Polynomial algebraic data type (α) *)
Inductive padt : expr -> Prop :=
| PUnitT : padt <{ 𝟙 }>
| PBool : padt <{ 𝔹 }>
| PProd α1 α2 : padt α1 -> padt α2 -> padt <{ α1 * α2 }>
| PSum α1 α2 : padt α1 -> padt α2 -> padt <{ α1 + α2 }>
| PGVar (X : atom) : padt <{ gvar X }>
.
Hint Constructors padt : padt.

(** ** OADT values (ω) *)
Inductive otval : expr -> Prop :=
| VUnitT : otval <{ 𝟙 }>
| VOBool : otval <{ ~𝔹 }>
| VProd ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 * ω2 }>
| VOSum ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 ~+ ω2 }>
.
Hint Constructors otval : otval.

(** ** Values (v) *)
Inductive val : expr -> Prop :=
| VUnitV : val <{ () }>
| VLit b : val <{ lit b }>
| VPair v1 v2 : val v1 -> val v2 -> val <{ (v1, v2) }>
| VAbs τ e : val <{ \:τ => e }>
| VInj b τ v : val v -> val <{ inj@b<τ> v }>
| VFold X v : val v -> val <{ fold<X> v }>
| VBoxedLit b : val <{ [b] }>
| VBoxedInj b ω v : otval ω -> val v -> val <{ [inj@b<ω> v] }>
.
Hint Constructors val : val.

(** ** OADT value typing *)
(** [oval v ω] means [v] is an oblivious value of oblivious type value [ω]. This
is essentially a subset of [typing], but we have it so that the dynamic
semantics does not depend on typing. *)
Inductive oval : expr -> expr -> Prop :=
| OVUnitV : oval <{ () }> <{ 𝟙 }>
| OVOBool b : oval <{ [b] }> <{ ~𝔹 }>
| OVPair v1 v2 ω1 ω2 :
    oval v1 ω1 -> oval v2 ω2 ->
    oval <{ (v1, v2) }> <{ ω1 * ω2 }>
| OVOSum b v ω1 ω2 :
    oval v <{ ite b ω1 ω2 }> ->
    (* Make sure the unused oblivious type is a value. *)
    otval <{ ite b ω2 ω1 }> ->
    oval <{ [inj@b<ω1 ~+ ω2> v] }> <{ ω1 ~+ ω2 }>
.
Hint Constructors oval : oval.

(** ** Syntactical well-formedness *)
(** Intuitively it means the boxed injection must be a value and it can be typed
by the annotated oblivious type value. This is useful for connecting the core
oblivious computation and the conceal phase: we assume the oblivious values
given by the conceal process are indeed well-formed. On the other hand, the
boxed injections produced by oblivious injections must be well-formed by our
small-step semantics. *)
Inductive expr_wf : expr -> Prop :=
| WfBVar k : expr_wf <{ bvar k }>
(* Conceptually we may choose to not consider free variables syntactically
well-formed. But it is more convenient to do so for the current purposes. *)
| WfFVar x : expr_wf <{ fvar x }>
| WfGVar x : expr_wf <{ gvar x }>
| WfPi τ1 τ2 :
    expr_wf τ1 ->
    expr_wf τ2 ->
    expr_wf <{ Π:τ1, τ2 }>
| WfAbs τ e :
    expr_wf τ ->
    expr_wf e ->
    expr_wf <{ \:τ => e }>
| WfLet e1 e2 :
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ let e1 in e2 }>
| WfCase l e0 e1 e2 :
    expr_wf e0 ->
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ case{l} e0 of e1 | e2 }>
| WfUnitT : expr_wf <{ 𝟙 }>
| WfBool l : expr_wf <{ 𝔹{l} }>
| WfProd τ1 τ2 :
    expr_wf τ1 ->
    expr_wf τ2 ->
    expr_wf <{ τ1 * τ2 }>
| WfSum l τ1 τ2 :
    expr_wf τ1 ->
    expr_wf τ2 ->
    expr_wf <{ τ1 +{l} τ2 }>
| WfApp e1 e2 :
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ e1 e2 }>
| WfUnitV : expr_wf <{ () }>
| WfLit b : expr_wf <{ lit b }>
| WfSec e :
    expr_wf e ->
    expr_wf <{ s𝔹 e }>
| WfIte l e0 e1 e2 :
    expr_wf e0 ->
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ if{l} e0 then e1 else e2 }>
| WfPair e1 e2 :
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ (e1, e2) }>
| WfProj b e :
    expr_wf e ->
    expr_wf <{ π@b e }>
| WfInj l b τ e :
    expr_wf τ ->
    expr_wf e ->
    expr_wf <{ inj{l}@b<τ> e }>
| WfFold X e :
    expr_wf e ->
    expr_wf <{ fold<X> e }>
| WfUnfold X e :
    expr_wf e ->
    expr_wf <{ unfold<X> e }>
| WfBoxedLit b :
    expr_wf <{ [b] }>
(* The only interesting case *)
| WfBoxedInj b ω v :
    oval <{ [inj@b<ω> v] }> ω ->
    expr_wf <{ [inj@b<ω> v] }>
.
Hint Constructors expr_wf: expr_wf.

(** ** Evaluation context (ℇ) *)
(* This style is inspired by Iron Lambda. *)
(** We define evaluation context [ℇ] as the hole-filling function. [ℇ e] fills
the hole in [ℇ] with [e]. [ectx ℇ] asserts that [ℇ] is a well-formed
context. *)
Inductive ectx : (expr -> expr) -> Prop :=
(* | CtxTop : ectx (fun e => e) *)
| CtxProd1 τ2 : ectx (fun τ1 => <{ τ1 * τ2 }>)
| CtxProd2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 * τ2 }>)
| CtxOSum1 τ2 : ectx (fun τ1 => <{ τ1 ~+ τ2 }>)
| CtxOSum2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 ~+ τ2 }>)
(** We reduce applications from right to left for some subtle reason. *)
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
Hint Constructors ectx : ectx.

(** ** Small-step relation *)
Section step.

Reserved Notation "e '-->!' e'" (at level 40).

Inductive step (Σ : gctx) : expr -> expr -> Prop :=
| SApp τ e v :
    val v ->
    <{ (\:τ => e) v }> -->! <{ e^v }>
| SLet v e :
    val v ->
    <{ let v in e }> -->! <{ e^v }>
| SCase b τ v e1 e2 :
    val v ->
    <{ case inj@b<τ> v of e1 | e2 }> -->! <{ ite b (e1^v) (e2^v) }>
(** The most interesting rule *)
| SOCase b ω1 ω2 v e1 e2 v1 v2 :
    (* TODO: do we need these 3 assumptions? *)
    otval ω1 -> otval ω2 -> val v ->
    oval v1 ω1 -> oval v2 ω2 ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
      <{ ~if [b] then (ite b (e1^v) (e1^v1)) else (ite b (e2^v2) (e2^v)) }>
| SAppOADT X τ e v :
    val v ->
    Σ !! X = Some (DOADT τ e) ->
    <{ (gvar X) v }> -->! <{ e^v }>
| SAppFun x τ e :
    Σ !! x = Some (DFun τ e) ->
    <{ gvar x }> -->! <{ e }>
| SOInj b ω v :
    otval ω -> val v ->
    <{ ~inj@b<ω> v }> -->! <{ [inj@b<ω> v] }>
| SIte b e1 e2 :
    <{ if b then e1 else e2 }> -->! <{ ite b e1 e2 }>
(** If we also want runtime obliviousness (e.g., against malicious adversaries),
we can check [v1] and [v2] are oblivious values in this rule. *)
| SMux b v1 v2 :
    val v1 -> val v2 ->
    <{ ~if [b] then v1 else v2 }> -->! <{ ite b v1 v2 }>
| SProj b v1 v2 :
    val v1 -> val v2 ->
    <{ π@b (v1, v2) }> -->! <{ ite b v1 v2 }>
| SFold X X' v :
    val v ->
    <{ unfold<X> (fold <X'> v) }> -->! v
| SSec b :
    <{ s𝔹 b }> -->! <{ [b] }>
(** Step under evaluation context *)
| SCtx ℇ e e' :
    ectx ℇ ->
    e -->! e' ->
    ℇ e -->! ℇ e'

where "e '-->!' e'" := (step _ e e').

End step.
Hint Constructors step : step.

(** Notations *)
Module semantics_notations.

Notation "Σ '⊨' e '-->!' e'" := (step Σ e e') (at level 40,
                                                e constr at level 0,
                                                e' constr at level 0).

Notation "Σ '⊨' e '-->*' e'" := (clos_refl_trans_1n _ (step Σ) e e')
                                  (at level 40,
                                   e constr at level 0,
                                   e' constr at level 0).

End semantics_notations.

End M.
