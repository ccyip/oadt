From oadt Require Import prelude.

(** The core language for oblivious algebraic data type. *)

Module oadt.

Section lang.

Context `{is_atom : Atom atom amap aset}.
Implicit Types (x X : atom) (L : aset).
Implicit Types (b : bool).

Open Scope type_scope.

(** * Syntax *)

(** ** Expressions (e, τ) *)
Inductive expr :=
(** Variables *)
| EBVar (k : nat)
| EFVar (x : atom)
| EGVar (x : atom)
(** Expressions with binders *)
| EPi (τ1 τ2: expr)
| EAbs (τ e : expr)
| ELet (e1 e2 : expr)
| ECase (e0 : expr) (e1 : expr) (e2 : expr)
| EOCase (e0 : expr) (e1 : expr) (e2 : expr)
(** Types *)
| EUnitT
| EBool
| EOBool
| EProd (τ1 τ2 : expr)
| ESum (τ1 τ2 : expr)
| EOSum (τ1 τ2 : expr)
(** Other expressions *)
| EApp (e1 e2 : expr)
| EUnitV
| ELit (b : bool)
| ESec (e : expr)
| ERet (e : expr)
| EIte (e0 e1 e2 : expr)
| EMux (e0 e1 e2 : expr)
| EPair (e1 e2 : expr)
| EProj (b : bool) (e : expr)
| EInj (b : bool) (τ e : expr)
| EOInj (b : bool) (τ e : expr)
| EFold (X : atom) (e : expr)
| EUnfold (X : atom) (e : expr)
(** Runtime expressions *)
| EBoxedLit (b : bool)
| EBoxedInj (b : bool) (τ e : expr)
.

(** ** GLobal definitions (D) *)
Variant gdef :=
| DADT (e : expr)
| DOADT (τ e : expr)
| DFun (τ e : expr)
.

(** ** Global named definitions (Ds) *)
Definition gdefs := list (atom * gdef).

(** ** Programs (P) *)
Definition program := gdefs * expr.

(** ** Global context (Σ) *)
(** It is used in operational semantics and typing. *)
Notation gctx := (amap gdef).

(** ** Notations *)
(* TODO: allow them to be used outside of this section. *)

(* Adapted from _Software Foundations_. *)
Coercion ELit : bool >-> expr.
Coercion EBVar : nat >-> expr.
(** This coercion should only be used in formalization. In the embedded language
for users, we should coerce [atom] to [EGVar]. *)
Coercion EFVar : atom >-> expr.

Declare Scope oadt_scope.
Delimit Scope oadt_scope with oadt.

Declare Custom Entry oadt.
Notation "<{ e }>" := e (e custom oadt at level 99).
Notation "( x )" := x (in custom oadt, x at level 99).
Notation "x" := x (in custom oadt at level 0, x constr at level 0).
Notation "'bvar' x" := (EBVar x) (in custom oadt at level 0, x constr at level 0,
                                     only parsing).
Notation "'fvar' x" := (EFVar x) (in custom oadt at level 0, x constr at level 0,
                                     only parsing).
Notation "'gvar' x" := (EGVar x) (in custom oadt at level 0, x constr at level 0).
Notation "'lit' b" := (ELit b) (in custom oadt at level 0, b constr at level 0,
                                   only parsing).
Notation "'𝟙'" := EUnitT (in custom oadt at level 0).
Notation "'Unit'" := EUnitT (in custom oadt at level 0, only parsing).
Notation "'𝔹'" := EBool (in custom oadt at level 0).
Notation "'Bool'" := EBool (in custom oadt at level 0, only parsing).
Notation "'~𝔹'" := EOBool (in custom oadt at level 0).
Notation "'~Bool'" := EOBool (in custom oadt at level 0, only parsing).
Notation "τ1 * τ2" := (EProd τ1 τ2) (in custom oadt at level 2,
                                        τ1 custom oadt,
                                        τ2 custom oadt at level 0).
Notation "τ1 + τ2" := (ESum τ1 τ2) (in custom oadt at level 3,
                                       left associativity).
Notation "τ1 ~+ τ2" := (EOSum τ1 τ2) (in custom oadt at level 3,
                                         left associativity).
Notation "'Π' : τ1 , τ2" := (EPi τ1 τ2) (in custom oadt at level 50,
                                            right associativity,
                                            format "Π : τ1 ,  τ2").
Notation "\ : τ '=>' e" := (EAbs τ e) (in custom oadt at level 90,
                                          τ custom oadt at level 99,
                                          e custom oadt at level 99,
                                          left associativity,
                                          format "\ : τ  =>  e").
Notation "e1 e2" := (EApp e1 e2) (in custom oadt at level 1, left associativity).
Notation "()" := EUnitV (in custom oadt at level 0).
Notation "( x , y , .. , z )" := (EPair .. (EPair x y) .. z)
                                   (in custom oadt at level 0,
                                       x custom oadt at level 99,
                                       y custom oadt at level 99,
                                       z custom oadt at level 99).
Notation "'π@' b e" := (EProj b e) (in custom oadt at level 0,
                                       b constr at level 0,
                                       e custom oadt at level 0,
                                       format "π@ b  e").
Notation "'π1' e" := (EProj true e) (in custom oadt at level 0,
                                        e custom oadt at level 0).
Notation "'π2' e" := (EProj false e) (in custom oadt at level 0,
                                         e custom oadt at level 0).
Notation "'s𝔹' e" := (ESec e) (in custom oadt at level 0,
                                  e custom oadt at level 0).
Notation "'r𝔹' e" := (ERet e) (in custom oadt at level 0,
                                  e custom oadt at level 0).
Notation "'if' e0 'then' e1 'else' e2" := (EIte e0 e1 e2)
                                            (in custom oadt at level 89,
                                                e0 custom oadt at level 99,
                                                e1 custom oadt at level 99,
                                                e2 custom oadt at level 99,
                                                left associativity).
Notation "'mux' e0 e1 e2" := (EMux e0 e1 e2) (in custom oadt at level 0,
                                                 e0 custom oadt at level 0,
                                                 e1 custom oadt at level 0,
                                                 e2 custom oadt at level 0).
Notation "'let' e1 'in' e2" := (ELet e1 e2)
                                 (in custom oadt at level 0,
                                     e1 custom oadt at level 99,
                                     e2 custom oadt at level 99).
Notation "'inj@' b < τ > e" := (EInj b τ e) (in custom oadt at level 0,
                                                b constr at level 0,
                                                τ custom oadt at level 0,
                                                e custom oadt at level 0,
                                                format "inj@ b < τ >  e").
Notation "'inl' < τ > e" := (EInj true τ e) (in custom oadt at level 0,
                                                τ custom oadt at level 0,
                                                e custom oadt at level 0,
                                                format "inl < τ >  e").
Notation "'inr' < τ > e" := (EInj false τ e) (in custom oadt at level 0,
                                                 τ custom oadt at level 0,
                                                 e custom oadt at level 0,
                                                 format "inr < τ >  e").
Notation "'~inj@' b < τ > e" := (EOInj b τ e) (in custom oadt at level 0,
                                                  b constr at level 0,
                                                  τ custom oadt at level 0,
                                                  e custom oadt at level 0,
                                                  format "~inj@ b < τ >  e").
Notation "'~inl' < τ > e" := (EOInj true τ e) (in custom oadt at level 0,
                                                  τ custom oadt at level 0,
                                                  e custom oadt at level 0,
                                                  format "~inl < τ >  e").
Notation "'~inr' < τ > e" := (EOInj false τ e) (in custom oadt at level 0,
                                                   τ custom oadt at level 0,
                                                   e custom oadt at level 0,
                                                   format "~inr < τ >  e").
Notation "'case' e0 'of' e1 '|' e2" :=
  (ECase e0 e1 e2) (in custom oadt at level 89,
                       e0 custom oadt at level 99,
                       e1 custom oadt at level 99,
                       e2 custom oadt at level 99,
                       left associativity).
Notation "'~case' e0 'of' e1 '|' e2" :=
  (EOCase e0 e1 e2) (in custom oadt at level 89,
                        e0 custom oadt at level 99,
                        e1 custom oadt at level 99,
                        e2 custom oadt at level 99,
                        left associativity).
Notation "'fold' < X > e" := (EFold X e) (in custom oadt at level 0,
                                             X custom oadt at level 0,
                                             e custom oadt at level 0,
                                             format "fold < X >  e").
Notation "'unfold' < X > e" := (EUnfold X e) (in custom oadt at level 0,
                                                 X custom oadt at level 0,
                                                 e custom oadt at level 0,
                                                 format "unfold < X >  e").
Notation "[ b ]" := (EBoxedLit b) (in custom oadt at level 0,
                                      b constr at level 0).
Notation "[ 'inj@' b < τ > e ]" := (EBoxedInj b τ e)
                                      (in custom oadt at level 0,
                                          b constr at level 0,
                                          τ custom oadt at level 0,
                                          e custom oadt at level 0,
                                          format "[ inj@ b < τ >  e ]").
Notation "[ 'inl' < τ > e ]" := (EBoxedInj true τ e)
                                   (in custom oadt at level 0,
                                       τ custom oadt at level 0,
                                       e custom oadt at level 0,
                                       format "[ inl < τ >  e ]").
Notation "[ 'inr' < τ > e ]" := (EBoxedInj false τ e)
                                   (in custom oadt at level 0,
                                       τ custom oadt at level 0,
                                       e custom oadt at level 0,
                                       format "[ inr < τ >  e ]").

Declare Custom Entry oadt_def.
Notation "D" := D (in custom oadt_def at level 0, D constr at level 0).
Notation "( D )" := D (in custom oadt_def, D at level 99).
Notation "'data' X := e" := (X, DADT e) (in custom oadt_def at level 0,
                                            X constr at level 0,
                                            e custom oadt at level 99).
Notation "'obliv' X ( : τ ) := e" := (X, DOADT τ e)
                                       (in custom oadt_def at level 0,
                                           X constr at level 0,
                                           τ custom oadt at level 99,
                                           e custom oadt at level 99,
                                           format "obliv  X  ( : τ )  :=  e").
Notation "'def' x : τ := e" := (x, DFun τ e) (in custom oadt_def at level 0,
                                                 x constr at level 0,
                                                 τ custom oadt at level 99,
                                                 e custom oadt at level 99).
Notation "[{ x }]" := (cons x nil)
                        (x custom oadt_def at level 99).
Notation "[{ x ; y ; .. ; z }]" := (cons x (cons y .. (cons z nil) ..))
                                     (x custom oadt_def at level 99,
                                      y custom oadt_def at level 99,
                                      z custom oadt_def at level 99,
                                      format "[{ '[v  ' '/' x ; '/' y ; '/' .. ; '/' z ']' '//' }]").

Notation "'ite' e0 e1 e2" := (if e0 then e1 else e2)
                               (in custom oadt at level 0,
                                    e0 constr at level 0,
                                    e1 custom oadt at level 0,
                                    e2 custom oadt at level 0).

(** * Examples *)
(* Axiom ℕ : atom. *)
(* Axiom pred : atom. *)
(* Example nat_example := [{ *)
(*   data ℕ := 𝟙 + ℕ; *)
(*   def pred : Π:ℕ, ℕ := \:ℕ => case unfold<ℕ> 0 of 1 | 0 *)
(* }]. *)

(** * Dynamic semantics *)

(** ** Variable opening  *)
Reserved Notation "'{' k '~>' s '}' e" (in custom oadt at level 20, k constr).

(* NOTE: recursively opening the types is probably not needed for [+] and [inj],
since their type arguments are always public, meaning that no bound variable is
possibly inside them. But I do it anyway for consistency, and possibly in the
future we allow oblivious types inside them. Let's see how this goes. I will
change it if it turns out to be too annoying for proofs. *)
Fixpoint open_ (k : nat) (s : expr) (e : expr) : expr :=
  match e with
  | <{ bvar n }> => if decide (k = n) then s else e
  | <{ Π:τ1, τ2 }> => <{ Π:{k~>s}τ1, {S k~>s}τ2 }>
  | <{ \:τ => e }> => <{ \:{k~>s}τ => {S k~>s}e }>
  | <{ let e1 in e2 }> => <{ let {k~>s}e1 in {S k~>s}e2 }>
  | <{ case e0 of e1 | e2 }> => <{ case {k~>s}e0 of {S k~>s}e1 | {S k~>s}e2 }>
  | <{ ~case e0 of e1 | e2 }> => <{ ~case {k~>s}e0 of {S k~>s}e1 | {S k~>s}e2 }>
  (** Congruence rules *)
  | <{ τ1 * τ2 }> => <{ ({k~>s}τ1) * ({k~>s}τ2) }>
  | <{ τ1 + τ2 }> => <{ ({k~>s}τ1) + ({k~>s}τ2) }>
  | <{ τ1 ~+ τ2 }> => <{ ({k~>s}τ1) ~+ ({k~>s}τ2) }>
  | <{ e1 e2 }> => <{ ({k~>s}e1) ({k~>s}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({k~>s}e) }>
  | <{ r𝔹 e }> => <{ r𝔹 ({k~>s}e) }>
  | <{ if e0 then e1 else e2 }> => <{ if {k~>s}e0 then {k~>s}e1 else {k~>s}e2 }>
  | <{ mux e0 e1 e2 }> => <{ mux ({k~>s}e0) ({k~>s}e1) ({k~>s}e2) }>
  | <{ (e1, e2) }> => <{ ({k~>s}e1, {k~>s}e2) }>
  | <{ π@b e }> => <{ π@b ({k~>s}e) }>
  | <{ inj@b<τ> e }> => <{ inj@b<({k~>s}τ)> ({k~>s}e) }>
  | <{ ~inj@b<τ> e }> => <{ ~inj@b<({k~>s}τ)> ({k~>s}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({k~>s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({k~>s}e) }>
  | _ => e
  end

where "'{' k '~>' s '}' e" := (open_ k s e) (in custom oadt).

Definition open s e := open_ 0 s e.

Notation "e ^ s" := (open s e) (in custom oadt at level 20).

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
    oval <{ [inj@b<ω1 ~+ ω2> v] }> <{ ω1 ~+ ω2 }>
.
Hint Constructors oval : oval.

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
| CtxRet : ectx (fun e => <{ r𝔹 e }>)
| CtxIte e1 e2 : ectx (fun e0 => <{ if e0 then e1 else e2 }>)
| CtxMux1 e1 e2 : ectx (fun e0 => <{ mux e0 e1 e2 }>)
| CtxMux2 v0 e2 : val v0 -> ectx (fun e1 => <{ mux v0 e1 e2 }>)
| CtxMux3 v0 v1 : val v0 -> val v1 -> ectx (fun e2 => <{ mux v0 v1 e2 }>)
| CtxPair1 e2 : ectx (fun e1 => <{ (e1, e2) }>)
| CtxPair2 v1 : val v1 -> ectx (fun e2 => <{ (v1, e2) }>)
| CtxProj b : ectx (fun e => <{ π@b e }>)
| CtxInj b τ : ectx (fun e => <{ inj@b<τ> e }>)
| CtxCase e1 e2: ectx (fun e0 => <{ case e0 of e1 | e2 }>)
| CtxOInj1 b e : ectx (fun τ => <{ ~inj@b<τ> e }>)
| CtxOInj2 b ω : otval ω -> ectx (fun e => <{ ~inj@b<ω> e }>)
| CtxOCase e1 e2: ectx (fun e0 => <{ ~case e0 of e1 | e2 }>)
| CtxFold X : ectx (fun e => <{ fold<X> e }>)
| CtxUnfold X : ectx (fun e => <{ unfold<X> e }>)
.
Hint Constructors ectx : ectx.

(** ** Small-step relation *)
Reserved Notation "e '-->!' e'" (at level 40).

Inductive step {Σ : gctx} : expr -> expr -> Prop :=
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
    otval ω1 -> otval ω2 -> val v ->
    oval v1 ω1 -> oval v2 ω2 ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
      <{ mux [b] (ite b (e1^v) (e1^v1)) (ite b (e2^v2) (e2^v)) }>
| SAppOADT X τ e v :
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
    <{ mux [b] v1 v2 }> -->! <{ ite b v1 v2 }>
| SProj b v1 v2 :
    val v1 -> val v2 ->
    <{ π@b (v1, v2) }> -->! <{ ite b v1 v2 }>
| SFold X X' v :
    val v ->
    <{ unfold<X> (fold <X'> v) }> -->! v
| SSec b :
    <{ s𝔹 b }> -->! <{ [b] }>
(** Delimited release [b] *)
| SRet b :
    <{ r𝔹 [b] }> -->! <{ b }>
(** Step under evaluation context *)
| SCtx ℇ e e' :
    ectx ℇ ->
    e -->! e' ->
    ℇ e -->! ℇ e'

where "e '-->!' e'" := (step e e').
Hint Constructors step : step.

Notation "Σ '⊨' e '-->!' e'" := (@step Σ e e') (at level 40,
                                                e constr at level 0,
                                                e' constr at level 0).

(** * Typing *)

(** ** Security level labels (l) *)
Variant label :=
| LAny
| LPublic
| LObliv
| LMixed
.

Declare Custom Entry oadt_label.
Notation "l" := l (in custom oadt_label at level 0, l constr at level 0).
Notation "( l )" := l (in custom oadt_label, l at level 99).
Notation "'A'" := (LAny) (in custom oadt_label at level 0).
Notation "'P'" := (LPublic) (in custom oadt_label at level 0).
Notation "'O'" := (LObliv) (in custom oadt_label at level 0).
Notation "'M'" := (LMixed) (in custom oadt_label at level 0).
Infix "⊔" := (⊔) (in custom oadt_label at level 50).

(** [label] has (semi-)lattice operators. *)

(** We define the partial order [⊑] on [label] directly as a computable
function. Alternatively, we may define an "immediate" relation as the kernel,
and then take its reflexive-transitive closure. But [label] is simple enough, so
let's do it in a simple way.

[l1 ⊑ l2] means [l2] is stricter than or as strict as [l1]. The relation can be
visualized as follow.

    M
   / \
  P   O
   \ /
    A
*)
Instance label_eq : EqDecision label.
Proof.
  unfold EqDecision, Decision.
  decide equality.
Defined.

Instance label_join : Join label :=
  fun l1 l2 =>
    match l1, l2 with
    | LAny, l | l, LAny => l
    | LPublic, LObliv | LObliv, LPublic => LMixed
    | LMixed, _ | _, LMixed => LMixed
    | l, _ => l
    end.

Instance label_le : SqSubsetEq label :=
  fun l1 l2 => l2 = (l1 ⊔ l2).

Instance label_top : Top label := LMixed.
Instance label_bot : Bottom label := LAny.

(** ** Kinds (κ) *)
(** We do not need kind abstraction. *)
Definition kind := label.

Notation "* @ l" := (l) (in custom oadt at level 0,
                            l custom oadt_label at level 0,
                            format "* @ l").

(** ** Typing context (Γ) *)
Notation tctx := (amap expr).

(** ** Expression equivalence *)
(** This definition is apparently unsound. But I use it as a placeholder for
now, so that I can figure out the necessary properties it should have. *)
Definition expr_equiv (Σ : gctx) (e e' : expr) : Prop := True.

Notation "Σ '⊢' e '≡' e'" := (expr_equiv Σ e e')
                               (at level 40,
                                e custom oadt at level 99,
                                e' custom oadt at level 99).

(** ** Expression typing and kinding *)
(** They are mutually defined. *)
Reserved Notation "Γ '⊢' e ':' τ" (at level 40,
                                   e custom oadt at level 99,
                                   τ custom oadt at level 99).
Reserved Notation "Γ '⊢' τ '::' κ" (at level 40,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

Inductive expr_typing {Σ : gctx} : tctx -> expr -> expr -> Prop :=
| TFVar Γ x τ :
    Γ !! x = Some τ ->
    Γ ⊢ fvar x : τ
| TGVar Γ x τ e :
    Σ !! x = Some (DFun τ e) ->
    Γ ⊢ gvar x : τ
| TAbs Γ e τ1 τ2 l L :
    (forall x, x ∉ L -> <[x:=τ2]>Γ ⊢ e^x : τ1) ->
    Γ ⊢ τ2 :: *@l ->
    Γ ⊢ \:τ2 => e : (Π:τ2, τ1)
| TLet Γ e1 e2 τ1 τ2 L :
    (forall x, x ∉ L -> <[x:=τ1]>Γ ⊢ e2^x : τ2) ->
    Γ ⊢ e1 : τ1 ->
    Γ ⊢ let e1 in e2 : τ2^e1
| TApp Γ e1 e2 τ1 τ2 :
    Γ ⊢ e1 : (Π:τ2, τ1) ->
    Γ ⊢ e2 : τ2 ->
    Γ ⊢ e1 e2 : τ1^e2
| TUnit Γ : Γ ⊢ () : 𝟙
| TLit Γ b : Γ ⊢ lit b : 𝔹
| TSec Γ e :
    Γ ⊢ e : 𝔹 ->
    Γ ⊢ s𝔹 e : ~𝔹
| TPair Γ e1 e2 τ1 τ2 :
    Γ ⊢ e1 : τ1 ->
    Γ ⊢ e2 : τ2 ->
    Γ ⊢ (e1, e2) : τ1 * τ2
| TMux Γ e0 e1 e2 τ :
    Γ ⊢ e0 : ~𝔹 ->
    Γ ⊢ e1 : τ ->
    Γ ⊢ e2 : τ ->
    Γ ⊢ τ :: *@O ->
    Γ ⊢ mux e0 e1 e2 : τ
| TProj Γ b e τ1 τ2 :
    Γ ⊢ e : τ1 * τ2 ->
    Γ ⊢ π@b e : ite b τ1 τ2
| TInj Γ b e τ1 τ2 :
    Γ ⊢ e : ite b τ1 τ2 ->
    Γ ⊢ τ1 + τ2 :: *@P ->
    Γ ⊢ inj@b<τ1 + τ2> e : τ1 + τ2
| TOInj Γ b e τ1 τ2 :
    Γ ⊢ e : ite b τ1 τ2 ->
    Γ ⊢ τ1 ~+ τ2 :: *@O ->
    Γ ⊢ ~inj@b<τ1 ~+ τ2> e : τ1 ~+ τ2
| TOCase Γ e0 e1 e2 τ1 τ2 τ L :
    (forall x, x ∉ L -> <[x:=τ1]>Γ ⊢ e1^x : τ) ->
    (forall x, x ∉ L -> <[x:=τ2]>Γ ⊢ e2^x : τ) ->
    Γ ⊢ e0 : τ1 ~+ τ2 ->
    Γ ⊢ τ :: *@O ->
    Γ ⊢ ~case e0 of e1 | e2 : τ
| TFold Γ X e τ :
    Σ !! X = Some (DADT τ) ->
    Γ ⊢ e : τ ->
    Γ ⊢ fold<X> e : gvar X
| TUnfold Γ X e τ :
    Σ !! X = Some (DADT τ) ->
    Γ ⊢ e : gvar X ->
    Γ ⊢ unfold<X> e : τ
(* TODO: [TIte] and [TCase] are not expressive enough. Need to infer the motive
and do substitution in [τ]. *)
| TIte Γ e0 e1 e2 τ :
    Γ ⊢ e0 : 𝔹 ->
    Γ ⊢ e1 : τ ->
    Γ ⊢ e2 : τ ->
    Γ ⊢ if e0 then e1 else e2 : τ
| TCase Γ e0 e1 e2 τ1 τ2 τ L :
    (forall x, x ∉ L -> <[x:=τ1]>Γ ⊢ e1^x : τ) ->
    (forall x, x ∉ L -> <[x:=τ2]>Γ ⊢ e2^x : τ) ->
    Γ ⊢ e0 : τ1 + τ2 ->
    Γ ⊢ case e0 of e1 | e2 : τ
| TConv Γ e τ τ' :
    Γ ⊢ e : τ' ->
    (* TODO: this assumption may be too strong. *)
    Γ ⊢ τ :: *@O ->
    Σ ⊢ τ' ≡ τ ->
    Γ ⊢ e : τ
(** Typing for runtime expressions is for metatheories. These expressions do not
appear in source programs. Plus, it is not possible to type them at runtime
since they are "encrypted" values. *)
| TBoxedLit Γ b : Γ ⊢ [b] : ~𝔹
| TBoxedInj Γ b v ω1 ω2 :
    (* TODO: use [oval] later *)
    Γ ⊢ v : ite b ω1 ω2 ->
    Γ ⊢ ω1 ~+ ω2 :: *@O ->
    val v ->
    otval <{ ω1 ~+ ω2 }> ->
    Γ ⊢ [inj@b<ω1 ~+ ω2> v] : ω1 ~+ ω2

where "Γ '⊢' e ':' τ" := (expr_typing Γ e τ)

with expr_kinding {Σ : gctx} : tctx -> expr -> kind -> Prop :=
| KVarADT Γ X τ :
    Σ !! X = Some (DADT τ) ->
    Γ ⊢ gvar X :: *@P
| KUnit Γ : Γ ⊢ 𝟙 :: *@A
| KBool Γ : Γ ⊢ 𝔹 :: *@P
| KOBool Γ : Γ ⊢ ~𝔹 :: *@O
| KPi Γ τ1 τ2 l1 l2 :
    Γ ⊢ τ1 :: *@l1 ->
    Γ ⊢ τ2 :: *@l2 ->
    Γ ⊢ (Π:τ1, τ2) :: *@M
| KApp Γ e τ X :
    Σ !! X = Some (DOADT τ e) ->
    Γ ⊢ e : τ ->
    Γ ⊢ (gvar X) e :: *@O
| KProd Γ τ1 τ2 l :
    Γ ⊢ τ1 :: *@l ->
    Γ ⊢ τ2 :: *@l ->
    Γ ⊢ τ1 * τ2 :: *@l
| KSum Γ τ1 τ2 l :
    Γ ⊢ τ1 :: *@l ->
    Γ ⊢ τ2 :: *@l ->
    Γ ⊢ τ1 + τ2 :: *@(l ⊔ P)
| KOSum Γ τ1 τ2 :
    Γ ⊢ τ1 :: *@O ->
    Γ ⊢ τ2 :: *@O ->
    Γ ⊢ τ1 ~+ τ2 :: *@O
| KIte Γ e0 τ1 τ2 :
    Γ ⊢ e0 : 𝔹 ->
    Γ ⊢ τ1 :: *@O ->
    Γ ⊢ τ2 :: *@O ->
    Γ ⊢ if e0 then τ1 else τ2 :: *@O
| KCase Γ e0 τ1 τ2 τ1' τ2' L :
    (forall x, x ∉ L -> <[x:=τ1']>Γ ⊢ τ1^x :: *@O) ->
    (forall x, x ∉ L -> <[x:=τ2']>Γ ⊢ τ2^x :: *@O) ->
    Γ ⊢ e0 : τ1' + τ2' ->
    Γ ⊢ case e0 of τ1 | τ2 :: *@O
| KLet Γ e τ τ' L :
    (forall x, x ∉ L -> <[x:=τ']>Γ ⊢ τ^x :: *@O) ->
    Γ ⊢ e : τ' ->
    Γ ⊢ let e in τ :: *@O
| KSub Γ τ l l' :
    Γ ⊢ τ :: *@l' ->
    l' ⊑ l ->
    Γ ⊢ τ :: *@l

where "Γ '⊢' τ '::' κ" := (expr_kinding Γ τ κ)
.
Hint Constructors expr_typing : expr_typing.
Hint Constructors expr_kinding : expr_kinding.

Notation "Σ ; Γ '⊢' e ':' τ" := (@expr_typing Σ Γ e τ)
                                  (at level 40,
                                   Γ constr at level 0,
                                   e custom oadt at level 99,
                                   τ custom oadt at level 99).
Notation "Σ ; Γ '⊢' τ '::' κ" := (@expr_kinding Σ Γ τ κ)
                                   (at level 40,
                                    Γ constr at level 0,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

Scheme expr_typing_kinding_ind := Minimality for expr_typing Sort Prop
  with expr_kinding_typing_ind := Minimality for expr_kinding Sort Prop.
Combined Scheme expr_typing_kinding_mutind
         from expr_typing_kinding_ind, expr_kinding_typing_ind.

(** ** Global definitions typing *)
Reserved Notation "Σ '=[' D ']=>' Σ'" (at level 40,
                                    D custom oadt_def at level 199).

Inductive gdef_typing : gctx -> (atom * gdef) -> gctx -> Prop :=
| TADT Σ X τ :
    Σ !! X = None ->
    <[X:=DADT τ]>Σ ; ∅ ⊢ τ :: *@P ->
    Σ =[ data X := τ ]=> <[X:=DADT τ]>Σ
| TOADT Σ X τ e L :
    Σ !! X = None ->
    Σ; ∅ ⊢ τ :: *@P ->
    (forall x, x ∉ L -> <[X:=DOADT τ e]>Σ ; ({[x:=τ]}) ⊢ e^x :: *@O) ->
    Σ =[ obliv X (:τ) := e ]=> <[X:=DOADT τ e]>Σ
| TFun Σ X τ e l :
    Σ !! X = None ->
    Σ; ∅ ⊢ τ :: *@l ->
    <[X:=DFun τ e]>Σ ; ∅ ⊢ e : τ ->
    Σ =[ def X : τ := e ]=> <[X:=DFun τ e]>Σ

where "Σ '=[' D ']=>' Σ'" := (gdef_typing Σ D Σ')
.
Hint Constructors gdef_typing : gdef_typing.

(* TODO: it would be nice to overload the notation of [gdef_typing]. Should be
doable with typeclass. *)
Reserved Notation "Σ '={' Ds '}=>' Σ'" (at level 40,
                                               Ds constr at level 99).

Inductive gdefs_typing : gctx -> gdefs -> gctx -> Prop :=
| TNil Σ : Σ ={ [] }=> Σ
| TCons Σ0 Σ1 Σ2 D Ds :
    Σ0 =[ D ]=> Σ1 ->
    Σ1 ={ Ds }=> Σ2 ->
    Σ0 ={ D::Ds }=> Σ2

where "Σ '={' Ds '}=>' Σ'" := (gdefs_typing Σ Ds Σ')
.
Hint Constructors gdefs_typing : gdefs_typing.

(** ** Program typing *)
(* TODO: notation? *)
Definition program_typing (p : program) (Σ : gctx) (τ : expr) :=
  match p with
  | (Ds, e) => ∅ ⊢ <{ Ds }> ▷ Σ /\ Σ; ∅ ⊢ e : τ
  end.

(** * Infrastructure *)

(** ** Locally closed *)
Inductive lc : expr -> Prop :=
| LCFVar x : lc <{ fvar x }>
| LCGVar x : lc <{ gvar x }>
| LCPi τ1 τ2 L :
    (forall x, x ∉ L -> lc <{ τ2^x }>) ->
    lc τ1 -> lc <{ Π:τ1, τ2 }>
| LCAbs τ e L :
    (forall x, x ∉ L -> lc <{ e^x }>) ->
    lc τ -> lc <{ \:τ => e }>
| LCLet e1 e2 L :
    (forall x, x ∉ L -> lc <{ e2^x }>) ->
    lc e1 -> lc <{ let e1 in e2 }>
| LCCase e0 e1 e2 L :
    (forall x, x ∉ L -> lc <{ e1^x }>) ->
    (forall x, x ∉ L -> lc <{ e2^x }>) ->
    lc e0 -> lc <{ case e0 of e1 | e2 }>
| LCOCase e0 e1 e2 L :
    (forall x, x ∉ L -> lc <{ e1^x }>) ->
    (forall x, x ∉ L -> lc <{ e2^x }>) ->
    lc e0 -> lc <{ ~case e0 of e1 | e2 }>
(** Congruence rules *)
| LCUnitT : lc <{ 𝟙 }>
| LCBool : lc <{ 𝔹 }>
| LCOBool : lc <{ ~𝔹 }>
| LCProd τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 * τ2 }>
| LCSum τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 + τ2 }>
| LCOSum τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 ~+ τ2 }>
| LCApp e1 e2 : lc e1 -> lc e2 -> lc <{ e1 e2 }>
| LCUnitV : lc <{ () }>
| LCLit b : lc <{ lit b }>
| LCSec e : lc e -> lc <{ s𝔹 e }>
| LCRet e : lc e -> lc <{ r𝔹 e }>
| LCIte e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ if e0 then e1 else e2 }>
| LCMux e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ mux e0 e1 e2 }>
| LCPair e1 e2 : lc e1 -> lc e2 -> lc <{ (e1, e2) }>
| LCProj b e : lc e -> lc <{ π@b e }>
| LCInj b τ e : lc τ -> lc e -> lc <{ inj@b<τ> e }>
| LCOInj b τ e : lc τ -> lc e -> lc <{ ~inj@b<τ> e }>
| LCFold X e : lc e -> lc <{ fold<X> e }>
| LCUnfold X e : lc e -> lc <{ unfold<X> e }>
| LCBoxedLit b : lc <{ [b] }>
| LCBoxedInj b τ e : lc τ -> lc e -> lc <{ [inj@b<τ> e] }>
.
Hint Constructors lc : lc.

(** ** Substitution (for local free variables) *)
Reserved Notation "'{' x '↦' s '}' e" (in custom oadt at level 20, x constr).
Fixpoint subst (x : atom) (s : expr) (e : expr) : expr :=
  match e with
  | <{ fvar y }> => if decide (x = y) then s else e
  (** Congruence rules *)
  | <{ Π:τ1, τ2 }> => <{ Π:{x↦s}τ1, {x↦s}τ2 }>
  | <{ \:τ => e }> => <{ \:{x↦s}τ => {x↦s}e }>
  | <{ let e1 in e2 }> => <{ let {x↦s}e1 in {x↦s}e2 }>
  | <{ case e0 of e1 | e2 }> => <{ case {x↦s}e0 of {x↦s}e1 | {x↦s}e2 }>
  | <{ ~case e0 of e1 | e2 }> => <{ ~case {x↦s}e0 of {x↦s}e1 | {x↦s}e2 }>
  | <{ τ1 * τ2 }> => <{ ({x↦s}τ1) * ({x↦s}τ2) }>
  | <{ τ1 + τ2 }> => <{ ({x↦s}τ1) + ({x↦s}τ2) }>
  | <{ τ1 ~+ τ2 }> => <{ ({x↦s}τ1) ~+ ({x↦s}τ2) }>
  | <{ e1 e2 }> => <{ ({x↦s}e1) ({x↦s}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({x↦s}e) }>
  | <{ r𝔹 e }> => <{ r𝔹 ({x↦s}e) }>
  | <{ if e0 then e1 else e2 }> => <{ if {x↦s}e0 then {x↦s}e1 else {x↦s}e2 }>
  | <{ mux e0 e1 e2 }> => <{ mux ({x↦s}e0) ({x↦s}e1) ({x↦s}e2) }>
  | <{ (e1, e2) }> => <{ ({x↦s}e1, {x↦s}e2) }>
  | <{ π@b e }> => <{ π@b ({x↦s}e) }>
  | <{ inj@b<τ> e }> => <{ inj@b<({x↦s}τ)> ({x↦s}e) }>
  | <{ ~inj@b<τ> e }> => <{ ~inj@b<({x↦s}τ)> ({x↦s}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({x↦s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({x↦s}e) }>
  | _ => e
  end

where "'{' x '↦' s '}' e" := (subst x s e) (in custom oadt).

(** ** Free variables *)
Fixpoint fv (e : expr) : aset :=
  match e with
  | <{ fvar x }> => {[x]}
  (* Congruence rules *)
  | <{ \:τ => e }>
  | <{ inj@_<τ> e }> | <{ ~inj@_<τ> e }> =>
    fv τ ∪ fv e
  | <{ Π:τ1, τ2 }> | <{ τ1 * τ2 }> | <{ τ1 + τ2 }> | <{ τ1 ~+ τ2 }> =>
    fv τ1 ∪ fv τ2
  | <{ let e1 in e2 }> | <{ (e1, e2) }> | <{ e1 e2 }> =>
    fv e1 ∪ fv e2
  | <{ case e0 of e1 | e2 }> | <{ ~case e0 of e1 | e2 }>
  | <{ if e0 then e1 else e2 }> | <{ mux e0 e1 e2 }> =>
    fv e0 ∪ fv e1 ∪ fv e2
  | <{ s𝔹 e }> | <{ r𝔹 e }> | <{ π@_ e }>
  | <{ fold<_> e }> | <{ unfold<_> e }> =>
    fv e
  | _ => ∅
  end.

Notation "x # e" := (x ∉ fv e) (at level 40).

Definition closed e := fv e = ∅.

Instance atom_stale : @Stale aset atom := singleton.
Arguments atom_stale /.

Instance aset_stale : Stale aset := id.
Arguments aset_stale /.

Instance expr_stale : Stale expr := fv.
Arguments expr_stale /.

Instance tctx_stale : Stale tctx := dom aset.
Arguments tctx_stale /.

Lemma open_lc_ e : forall s u i j,
  <{ {j~>u}({i~>s}e) }> = <{ {i~>s}e }> ->
  i <> j ->
  <{ {j~>u}e }> = e.
Proof.
  induction e; hauto.
Qed.

(** Open a locally-closed expression does not change it. *)
Lemma open_lc e : forall s,
  lc e -> forall k, <{ {k~>s}e }> = e.
Proof.
  induction 1; try hauto;
    (* expressions with binders *)
    simpl_cofin; hauto use: open_lc_.
Qed.

Lemma subst_fresh e : forall x s,
  x # e -> <{ {x↦s}e }> = e.
Proof.
  induction e; hauto simp+: set_unfold.
Qed.

Lemma subst_open_distr e : forall x s v,
  lc s ->
  <{ {x↦s}(e^v) }> = <{ ({x↦s}e)^({x↦s}v) }>.
Proof.
  unfold open. generalize 0.
  induction e; hauto use: open_lc.
Qed.

Lemma subst_open_comm e : forall x y s,
  x <> y ->
  lc s ->
  <{ {x↦s}(e^y) }> = <{ ({x↦s}e)^y }>.
Proof.
  qauto use: subst_open_distr.
Qed.

(** We may prove this one using [subst_open_distr] and [subst_fresh], but a
direct induction gives us a slightly stronger version (without the local closure
constraint). *)
Lemma subst_intro e : forall s x,
  x # e ->
  <{ e^s }> = <{ {x↦s}(e^x) }>.
Proof.
  unfold open. generalize 0.
  induction e; hauto simp+: set_unfold.
Qed.

(** Well-typed and well-kinded expressions are locally closed. *)
Lemma expr_typing_lc Σ Γ e τ :
  Σ; Γ ⊢ e : τ ->
  lc e
with expr_kinding_lc  Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  lc τ.
Proof.
  (* Technically we only need [destruct] here, but it is easier for automation
  to construct a non-well-founded proof. *)
  all : induction 1; try hauto ctrs: lc.
  econstructor; eauto.
  simpl_cofin.
  hauto unfold: open use: open_lc.
Qed.

(** This lemma is equivalent to [SCtx] constructor, but more friendly for
automation. *)
Lemma SCtx' {Σ} ℇ e e' E E' :
    Σ ⊨ e -->! e' ->
    ℇ e = E ->
    ℇ e' = E' ->
    ectx ℇ ->
    Σ ⊨ E -->! E'.
Proof.
  hauto ctrs: step.
Qed.
Hint Resolve SCtx' : ectx.

Hint Extern 0 (?f ?a = ?b) => higher_order_reflexivity : ectx.

(** * Metatheories *)

(** ** Properties of labels  *)
(* TODO: organize them in a type class. *)
Lemma label_join_comm (l1 l2 : label) :
  l1 ⊔ l2 = l2 ⊔ l1.
Proof.
  destruct l1, l2; auto.
Qed.

Lemma label_join_assoc (l1 l2 l3 : label) :
  l1 ⊔ (l2 ⊔ l3) = (l1 ⊔ l2) ⊔ l3.
Proof.
  destruct l1, l2, l3; auto.
Qed.

Lemma label_join_idempotent (l : label) :
  l ⊔ l = l.
Proof.
  destruct l; auto.
Qed.

Lemma label_top_dominant_r (l : label) :
  l ⊔ ⊤ = ⊤.
Proof.
  destruct l; auto.
Qed.

Lemma label_bot_identity_r (l : label) :
  l ⊔ ⊥ = l.
Proof.
  destruct l; auto.
Qed.

Lemma label_join_consistent (l1 l2 : label) :
  l1 ⊑ l2 <-> l2 = l1 ⊔ l2.
Proof.
  reflexivity.
Qed.

(* TODO: try aac rewrite and other automation for a tactic simpl_semilattice. *)

(* TODO: move them to another file. The following lemmas of label can be
derived from the previous "axioms". *)

Lemma label_top_dominant_l (l : label) :
  ⊤ ⊔ l = ⊤.
Proof.
  scongruence use: label_top_dominant_r, label_join_comm.
Qed.

Lemma label_bot_identity_l (l : label) :
  ⊥ ⊔ l = l.
Proof.
  scongruence use: label_bot_identity_r, label_join_comm.
Qed.

Lemma label_join_is_lub (l1 l2 l : label) :
  l1 ⊑ l -> l2 ⊑ l -> l1 ⊔ l2 ⊑ l.
Proof.
  scongruence use: label_join_consistent, label_join_assoc.
Qed.

Lemma label_join_prime (l1 l2 l : label) :
  l ⊑ l1 -> l ⊑ l2 -> l ⊑ l1 ⊔ l2.
Proof.
  scongruence use: label_join_consistent, label_join_assoc.
Qed.

Lemma label_join_le_l (l1 l2 : label) :
  l1 ⊑ l1 ⊔ l2.
Proof.
  scongruence use: label_join_consistent, label_join_assoc, label_join_idempotent.
Qed.

Lemma label_join_le_r (l1 l2 : label) :
  l2 ⊑ l1 ⊔ l2.
Proof.
  scongruence use: label_join_le_l, label_join_comm.
Qed.

Lemma label_top_le (l : label) :
  l ⊑ ⊤.
Proof.
  scongruence use: label_join_consistent, label_top_dominant_r.
Qed.

Lemma label_bot_le (l : label) :
  ⊥ ⊑ l.
Proof.
  sfirstorder use: label_join_consistent, label_top_dominant_r.
Qed.

Lemma label_top_inv (l : label) :
  ⊤ ⊑ l -> l = ⊤.
Proof.
  scongruence use: label_join_consistent, label_top_dominant_l.
Qed.

Lemma label_bot_inv (l : label) :
  l ⊑ ⊥ -> l = ⊥.
Proof.
  scongruence use: label_join_consistent, label_bot_identity_r.
Qed.

Lemma label_join_bot_iff (l1 l2 : label) :
  l1 ⊔ l2 = ⊥ <-> l1 = ⊥ /\ l2 = ⊥.
Proof.
  split.
  - intros.
    assert (l1 ⊔ (l1 ⊔ l2) = l1 ⊔ ⊥ /\ l2 ⊔ (l1 ⊔ l2) = l2 ⊔ ⊥)
      by sfirstorder.
    scongruence use: label_join_assoc, label_join_comm, label_join_idempotent,
                     label_bot_identity_r.
  - qauto.
Qed.

Instance label_le_po : @PartialOrder label (⊑).
Proof.
  repeat split;
    scongruence use: label_join_consistent,
                     label_join_idempotent,
                     label_join_assoc,
                     label_join_comm.
Qed.

(** We can always find an inhabitant for any oblivious type value. *)
Lemma oval_inhabited ω :
  otval ω ->
  exists v, oval v ω.
Proof.
  induction 1; try qauto ctrs: oval.
  (* Case [~+]: we choose left injection as inhabitant. *)
  sfirstorder use: (OVOSum true).
Qed.

(** ** Kind inversion  *)
Ltac kind_inv_solver :=
  match goal with
  | |- _; _ ⊢ ?τ :: _ -> _ => remember τ
  end;
  induction 1; subst; try scongruence; qauto inv: label.

Lemma kind_inv_pi Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ Π:τ1, τ2 :: κ -> κ = <{ *@M }>.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_bool Σ Γ κ :
  Σ; Γ ⊢ 𝔹 :: κ -> κ = <{ *@P }> \/ κ = <{ *@M }>.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sum Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ τ1 + τ2 :: κ -> κ = <{ *@P }> \/ κ = <{ *@M }>.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_gvar Σ Γ x κ :
  Σ; Γ ⊢ gvar x :: κ -> κ = <{ *@P }> \/ κ = <{ *@M }>.
Proof.
  kind_inv_solver.
Qed.

(** ** Canonical forms *)
Lemma canonical_form_abs Σ e τ2 τ1 :
  Σ; ∅ ⊢ e : Π:τ2, τ1 ->
  val e ->
  exists e' τ, e = <{ \:τ => e' }>.
Proof.
  inversion 1; inversion 1; qauto use: kind_inv_pi.
Qed.
Hint Resolve canonical_form_abs : canonical_forms.

Lemma canonical_form_bool Σ e :
  Σ; ∅ ⊢ e : 𝔹 ->
  val e ->
  exists b, e = <{ b }>.
Proof.
  inversion 1; inversion 1; eauto; qauto use: kind_inv_bool.
Qed.
Hint Resolve canonical_form_bool : canonical_forms.

Lemma canonical_form_obool Σ e :
  Σ; ∅ ⊢ e : ~𝔹 ->
  val e ->
  exists b, e = <{ [b] }>.
Proof.
  Admitted.
Hint Resolve canonical_form_obool : canonical_forms.

Lemma canonical_form_prod Σ e τ1 τ2 :
  Σ; ∅ ⊢ e : τ1 * τ2 ->
  val e ->
  exists v1 v2, val v1 /\ val v2 /\ e = <{ (v1, v2) }>.
Proof.
  Admitted.
Hint Resolve canonical_form_prod : canonical_forms.

Lemma canonical_form_sum Σ e τ1 τ2 :
  Σ; ∅ ⊢ e : τ1 + τ2 ->
  val e ->
  exists b v τ, val v /\ e = <{ inj@b<τ> v }>.
Proof.
  inversion 1; inversion 1; eauto; qauto use: kind_inv_sum.
Qed.
Hint Resolve canonical_form_sum : canonical_forms.

Lemma canonical_form_osum Σ e τ1 τ2 :
  Σ; ∅ ⊢ e : τ1 ~+ τ2 ->
  val e ->
  exists b v ω1 ω2, val v /\ otval ω1 /\ otval ω2 /\
               e = <{ [inj@b<ω1 ~+ ω2> v] }>.
Proof.
  Admitted.
Hint Resolve canonical_form_osum : canonical_forms.

(** Though it seems we should have a condition of [X] being an (public) ADT, this
condition is not needed since it is implied by the typing judgment. *)
Lemma canonical_form_fold Σ e X :
  Σ; ∅ ⊢ e : gvar X ->
  val e ->
  exists v X', val v /\ e = <{ fold<X'> v }>.
Proof.
  inversion 1; inversion 1; eauto; qauto use: kind_inv_gvar.
Qed.
Hint Resolve canonical_form_fold : canonical_forms.

(** ** Properties of kinding  *)
Lemma any_kind_otval Σ Γ τ :
  Σ; Γ ⊢ τ :: *@A ->
  otval τ.
Proof.
  remember <{ *@A }>.
  induction 1; subst; try hauto ctrs: otval.
  - rewrite label_join_bot_iff in *. easy.
  - eauto using label_bot_inv.
Qed.

(** ** Progress *)

Theorem progress_ Ds Σ :
  ∅ ={ Ds }=> Σ ->
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      Γ = ∅ ->
      val e \/ exists e', Σ ⊨ e -->! e') /\
  (forall Γ τ κ,
     Σ; Γ ⊢ τ :: κ ->
     Γ = ∅ ->
     κ = <{ *@O }> ->
     otval τ \/ exists τ', Σ ⊨ τ -->! τ').
Proof.
  intros Hd.
  apply expr_typing_kinding_mutind; intros; subst;
    (* If a type is not used in the conclusion, the mutual inductive hypothesis
    for it is useless. Remove this hypothesis to avoid slowdown the
    automation. *)
    try match goal with
        | H : context [otval ?τ \/ _] |- val ?e \/ _ =>
          assert_fails contains e τ; clear H
        end;
    (* Try solve the boring cases, unless they are the trickier ones. *)
    (* TODO: the automation here is really slow. *)
    first [ goal_is (val <{ ~case _ of _ | _ }> \/ _)
          | goal_is (otval <{ _ + _ }> \/ _)
          (* Take care of the simple cases. *)
          | hauto simp: simpl_map
                  ctrs: val, otval, step, ectx
          (* Take care of the more complex cases involving evaluation context. *)
          (* For expression progress. *)
          | goal_contains val;
            hauto ctrs: val, step
                  solve+: (eauto with ectx)
                  use: canonical_form_abs,
                       canonical_form_bool,
                       canonical_form_obool,
                       canonical_form_prod,
                       canonical_form_sum,
                       canonical_form_fold
          (* For oblivious type progress. *)
          | goal_contains otval;
            hauto ctrs: otval, step
                  solve+: (eauto with ectx)
                  use: canonical_form_bool,
                       canonical_form_sum
          | idtac ].

  (* [~case _ of _ | _] *)
  - right. intuition.
    (* Discriminee is value. *)
    + select (_; _ ⊢ _ : _) (fun H => apply canonical_form_osum in H); eauto.
      sintuition.
      select! (otval _) (fun H => use (oval_inhabited _ H)).
      hauto ctrs: step.
    (* Discriminee can take a step. *)
    + hauto solve+: (eauto with ectx) ctrs: step.

  (* [_ + _]. This case is impossible. *)
  - enough (<{ *@P }> ⊑ <{ *@O }>). easy.
    unfold kind in *.
    select! (_ = <{ *@O }>) (fun H => rewrite <- H).
    hauto use: label_join_le_r.

  (* Kinding subsumption *)
  - destruct (_ : kind); by eauto using any_kind_otval.
Qed.

Theorem progress Ds Σ τ e :
  ∅ ={ Ds }=> Σ ->
  Σ; ∅ ⊢ e : τ ->
  val e \/ exists e', Σ ⊨ e -->! e'.
Proof.
  hauto use: progress_.
Qed.

End lang.

End oadt.
