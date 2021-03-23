From oadt Require Import prelude.

(** The core language for oblivious algebraic data type. *)

Module oadt.

Section lang.

Context `{is_atom : Atom atom amap aset}.
Implicit Types (x X y Y : atom) (L : aset).
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
Notation program := (gdefs * expr).

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
| WfCase e0 e1 e2 :
    expr_wf e0 ->
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ case e0 of e1 | e2 }>
| WfOCase e0 e1 e2 :
    expr_wf e0 ->
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ ~case e0 of e1 | e2 }>
| WfUnitT : expr_wf <{ 𝟙 }>
| WfBool : expr_wf <{ 𝔹 }>
| WfOBool : expr_wf <{ ~𝔹 }>
| WfProd τ1 τ2 :
    expr_wf τ1 ->
    expr_wf τ2 ->
    expr_wf <{ τ1 * τ2 }>
| WfSum τ1 τ2 :
    expr_wf τ1 ->
    expr_wf τ2 ->
    expr_wf <{ τ1 + τ2 }>
| WfOSum τ1 τ2 :
    expr_wf τ1 ->
    expr_wf τ2 ->
    expr_wf <{ τ1 ~+ τ2 }>
| WfApp e1 e2 :
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ e1 e2 }>
| WfUnitV : expr_wf <{ () }>
| WfLit b : expr_wf <{ lit b }>
| WfSec e :
    expr_wf e ->
    expr_wf <{ s𝔹 e }>
| WfRet e :
    expr_wf e ->
    expr_wf <{ r𝔹 e }>
| WfIte e0 e1 e2 :
    expr_wf e0 ->
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ if e0 then e1 else e2 }>
| WfMux e0 e1 e2 :
    expr_wf e0 ->
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ mux e0 e1 e2 }>
| WfPair e1 e2 :
    expr_wf e1 ->
    expr_wf e2 ->
    expr_wf <{ (e1, e2) }>
| WfProj b e :
    expr_wf e ->
    expr_wf <{ π@b e }>
| WfInj b τ e :
    expr_wf τ ->
    expr_wf e ->
    expr_wf <{ inj@b<τ> e }>
| WfOInj b τ e :
    expr_wf τ ->
    expr_wf e ->
    expr_wf <{ ~inj@b<τ> e }>
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

(** ** Indistinguishability *)
(** Instead of formalizing an observe function and considering two expressions
indistinguishable if they are observed the same, we directly formalize the
indistinguishability relation between two expressions as the equivalence induced
by the observe function. *)
Reserved Notation "e '≈' e'" (at level 40).
(** All rules but the rules for boxed expressions are just congruence rules.
Some rules are not necessary if the expressions are well-typed, but we include
them anyway. *)
Inductive indistinguishable : expr -> expr -> Prop :=
| IBVar k : <{ bvar k }> ≈ <{ bvar k }>
| IFVar x : <{ fvar x }> ≈ <{ fvar x }>
| IGVar x : <{ gvar x }> ≈ <{ gvar x }>
| IPi τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ Π:τ1, τ2 }> ≈ <{ Π:τ1', τ2' }>
| IAbs τ τ' e e' :
    τ ≈ τ' ->
    e ≈ e' ->
    <{ \:τ => e }> ≈ <{ \:τ' => e' }>
| ILet e1 e1' e2 e2' :
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ let e1 in e2 }> ≈ <{ let e1' in e2' }>
| ICase e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ case e0 of e1 | e2 }> ≈ <{ case e0' of e1' | e2' }>
| IOCase e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ ~case e0 of e1 | e2 }> ≈ <{ ~case e0' of e1' | e2' }>
| IUnitT : <{ 𝟙 }> ≈ <{ 𝟙 }>
| IBool : <{ 𝔹 }> ≈ <{ 𝔹 }>
| IOBool : <{ ~𝔹 }> ≈ <{ ~𝔹 }>
| IProd τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ τ1 * τ2 }> ≈ <{ τ1' * τ2' }>
| ISum τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ τ1 + τ2 }> ≈ <{ τ1' + τ2' }>
| IOSum τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ τ1 ~+ τ2 }> ≈ <{ τ1' ~+ τ2' }>
| IApp e1 e1' e2 e2' :
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ e1 e2 }> ≈ <{ e1' e2' }>
| IUnitV : <{ () }> ≈ <{ () }>
| ILit b : <{ lit b }> ≈ <{ lit b }>
| ISec e e' :
    e ≈ e' ->
    <{ s𝔹 e }> ≈ <{ s𝔹 e' }>
| IRet e e' :
    e ≈ e' ->
    <{ r𝔹 e }> ≈ <{ r𝔹 e' }>
| IIte e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ if e0 then e1 else e2 }> ≈ <{ if e0' then e1' else e2' }>
| IMux e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ mux e0 e1 e2 }> ≈ <{ mux e0' e1' e2' }>
| IPair e1 e1' e2 e2' :
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ (e1, e2) }> ≈ <{ (e1', e2') }>
| IProj b e e' :
    e ≈ e' ->
    <{ π@b e }> ≈ <{ π@b e' }>
| IInj b b' τ τ' e e' :
    τ ≈ τ' ->
    e ≈ e' ->
    <{ inj@b<τ> e }> ≈ <{ inj@b<τ'> e' }>
| IOInj b τ τ' e e' :
    τ ≈ τ' ->
    e ≈ e' ->
    <{ ~inj@b<τ> e }> ≈ <{ ~inj@b<τ'> e' }>
| IFold X e e' :
    e ≈ e' ->
    <{ fold<X> e }> ≈ <{ fold<X> e' }>
| IUnfold X e e' :
    e ≈ e' ->
    <{ unfold<X> e }> ≈ <{ unfold<X> e' }>
(* The only interesting cases *)
| IBoxedLit b b' :
    (* We can not distinguish between two encrypted boolean values. *)
    <{ [b] }> ≈ <{ [b'] }>
| IBoxedInj b b' τ e e' :
    (* We can not tell which branch an encrypted sum injects to nor what the
    encrypted value is. But the type information is public so we need to make
    sure nothing leaked from this type information. Technically we only need the
    two types to be indistinguishable, but the stronger notion of equality also
    works. *)
    <{ [inj@b<τ> e] }> ≈ <{ [inj@b'<τ> e'] }>

where "e '≈' e'" := (indistinguishable e e').

Hint Constructors indistinguishable : indistinguishable.

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

Notation "Σ '⊨' e '-->*' e'" := (clos_refl_trans_1n _ (@step Σ) e e')
                                  (at level 40,
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

Notation "*@A" := (LAny) (in custom oadt at level 0).
Notation "*@P" := (LPublic) (in custom oadt at level 0).
Notation "*@O" := (LObliv) (in custom oadt at level 0).
Notation "*@M" := (LMixed) (in custom oadt at level 0).
Notation "*@ l" := (l) (in custom oadt at level 0,
                            format "*@ l").
Notation "*@( l ⊔ 'P' )" := (l ⊔ LPublic)
                              (in custom oadt at level 0,
                                  format "*@( l  ⊔  'P' )").
Notation "*@( l1 ⊔ l2 )" := (l1 ⊔ l2)
                              (in custom oadt at level 0,
                                  format "*@( l1  ⊔  l2 )").

(** ** Typing context (Γ) *)
Notation tctx := (amap expr).

(** ** Expression equivalence *)
(** Type equivalence is a placeholder for now. *)
Parameter expr_equiv : gctx -> expr -> expr -> Prop.

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

Inductive typing {Σ : gctx} : tctx -> expr -> expr -> Prop :=
| TFVar Γ x τ κ :
    Γ !! x = Some τ ->
    Γ ⊢ τ :: κ ->
    Γ ⊢ fvar x : τ
| TGVar Γ x τ e :
    Σ !! x = Some (DFun τ e) ->
    Γ ⊢ gvar x : τ
| TAbs Γ e τ1 τ2 l L :
    (forall x, x ∉ L -> <[x:=τ2]>Γ ⊢ e^x : τ1^x) ->
    Γ ⊢ τ2 :: *@l ->
    Γ ⊢ \:τ2 => e : (Π:τ2, τ1)
| TLet Γ e1 e2 τ1 τ2 L :
    (forall x, x ∉ L -> <[x:=τ1]>Γ ⊢ e2^x : τ2^x) ->
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
| TOCase Γ e0 e1 e2 τ1 τ2 τ L1 L2 :
    (forall x, x ∉ L1 -> <[x:=τ1]>Γ ⊢ e1^x : τ) ->
    (forall x, x ∉ L2 -> <[x:=τ2]>Γ ⊢ e2^x : τ) ->
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
| TCase Γ e0 e1 e2 τ1 τ2 τ κ L1 L2 :
    (forall x, x ∉ L1 -> <[x:=τ1]>Γ ⊢ e1^x : τ) ->
    (forall x, x ∉ L2 -> <[x:=τ2]>Γ ⊢ e2^x : τ) ->
    Γ ⊢ e0 : τ1 + τ2 ->
    Γ ⊢ τ :: κ ->
    Γ ⊢ case e0 of e1 | e2 : τ
(** Typing for runtime expressions is for metatheories. These expressions do not
appear in source programs. Plus, it is not possible to type them at runtime
since they are "encrypted" values. *)
| TBoxedLit Γ b : Γ ⊢ [b] : ~𝔹
| TBoxedInj Γ b v ω :
    oval <{ [inj@b<ω> v] }> ω ->
    Γ ⊢ [inj@b<ω> v] : ω
(** Type conversion *)
| TConv Γ e τ τ' κ :
    Γ ⊢ e : τ' ->
    Γ ⊢ τ :: κ ->
    Σ ⊢ τ' ≡ τ ->
    Γ ⊢ e : τ
where "Γ '⊢' e ':' τ" := (typing Γ e τ)

with kinding {Σ : gctx} : tctx -> expr -> kind -> Prop :=
| KVarADT Γ X τ :
    Σ !! X = Some (DADT τ) ->
    Γ ⊢ gvar X :: *@P
| KUnit Γ : Γ ⊢ 𝟙 :: *@A
| KBool Γ : Γ ⊢ 𝔹 :: *@P
| KOBool Γ : Γ ⊢ ~𝔹 :: *@O
| KPi Γ τ1 τ2 l1 l2 L :
    (forall x, x ∉ L -> <[x:=τ1]>Γ ⊢ τ2^x :: *@l2) ->
    Γ ⊢ τ1 :: *@l1 ->
    Γ ⊢ (Π:τ1, τ2) :: *@M
| KApp Γ e' e τ X :
    Σ !! X = Some (DOADT τ e') ->
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
| KCase Γ e0 τ1 τ2 τ1' τ2' L1 L2 :
    (forall x, x ∉ L1 -> <[x:=τ1']>Γ ⊢ τ1^x :: *@O) ->
    (forall x, x ∉ L2 -> <[x:=τ2']>Γ ⊢ τ2^x :: *@O) ->
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

where "Γ '⊢' τ '::' κ" := (kinding Γ τ κ)
.
Hint Constructors typing : typing.
Hint Constructors kinding : kinding.

Notation "Σ ; Γ '⊢' e ':' τ" := (@typing Σ Γ e τ)
                                  (at level 40,
                                   Γ constr at level 0,
                                   e custom oadt at level 99,
                                   τ custom oadt at level 99).
Notation "Σ ; Γ '⊢' τ '::' κ" := (@kinding Σ Γ τ κ)
                                   (at level 40,
                                    Γ constr at level 0,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

Scheme typing_kinding_ind := Minimality for typing Sort Prop
  with kinding_typing_ind := Minimality for kinding Sort Prop.
Combined Scheme typing_kinding_mutind
         from typing_kinding_ind, kinding_typing_ind.

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
Definition program_typing (Ds : gdefs) (e : expr) (Σ : gctx) (τ : expr) :=
  ∅ ={ Ds }=> Σ /\ Σ; ∅ ⊢ e : τ.

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
| LCCase e0 e1 e2 L1 L2 :
    (forall x, x ∉ L1 -> lc <{ e1^x }>) ->
    (forall x, x ∉ L2 -> lc <{ e2^x }>) ->
    lc e0 -> lc <{ case e0 of e1 | e2 }>
| LCOCase e0 e1 e2 L1 L2 :
    (forall x, x ∉ L1 -> lc <{ e1^x }>) ->
    (forall x, x ∉ L2 -> lc <{ e2^x }>) ->
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

Notation "{ x '↦' s }" := (subst x s).

(** ** Free variables *)
Fixpoint fv (e : expr) : aset :=
  match e with
  | <{ fvar x }> => {[x]}
  (* Congruence rules *)
  | <{ \:τ => e }>
  | <{ inj@_<τ> e }> | <{ ~inj@_<τ> e }> | <{ [inj@_<τ> e] }> =>
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

Definition tctx_fv : tctx -> aset :=
  map_fold (fun x τ S => fv τ ∪ S) ∅.

Definition closed e := fv e ≡ ∅.

Instance atom_stale : @Stale aset atom := singleton.
Arguments atom_stale /.

Instance aset_stale : Stale aset := id.
Arguments aset_stale /.

Instance expr_stale : Stale expr := fv.
Arguments expr_stale /.

Instance tctx_stale : Stale tctx := fun Γ => dom aset Γ ∪ tctx_fv Γ.
Arguments tctx_stale /.

Notation "x # s" := (x ∉ stale s) (at level 40).
Arguments stale /.

(** ** Well-formedness of [gctx] *)
Definition gctx_wf (Σ : gctx) :=
  map_Forall (fun _ D =>
                match D with
                | DADT τ =>
                  Σ; ∅ ⊢ τ :: *@P
                | DOADT τ e =>
                  Σ; ∅ ⊢ τ :: *@P /\
                  exists L, forall x, x ∉ L -> Σ; ({[x:=τ]}) ⊢ e^x :: *@O
                | DFun τ e =>
                  Σ; ∅ ⊢ e : τ /\
                  exists l, Σ; ∅ ⊢ τ :: *@l
                end) Σ.

(* NOTE: [inversion] is the culprit for the slowness of this proof. *)
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
  induction 1; try scongruence;
    (* expressions with binders *)
    simpl_cofin; hauto use: open_lc_.
Qed.

Lemma open_lc_intro e s :
  lc e -> <{ e^s }> = e.
Proof.
  unfold open.
  qauto use: open_lc.
Qed.

Lemma subst_fresh e : forall x s,
  x # e -> <{ {x↦s}e }> = e.
Proof.
  induction e; simpl; intros; f_equal;
    (* Case analysis for [EFVar] case *)
    try case_split; subst;
    try auto_apply; fast_set_solver!.
Qed.

Lemma subst_open_distr e : forall x s v,
  lc s ->
  <{ {x↦s}(e^v) }> = <{ ({x↦s}e)^({x↦s}v) }>.
Proof.
  unfold open. generalize 0.
  induction e; try qauto rew: off use: open_lc; qauto use: open_lc.
Qed.

Lemma subst_open_comm e : forall x y s,
  x <> y ->
  lc s ->
  <{ {x↦s}(e^y) }> = <{ ({x↦s}e)^y }>.
Proof.
  qauto use: subst_open_distr.
Qed.

Lemma subst_trans x y s e :
  y # e ->
  {y↦s}({x↦y}e) = {x↦s}e.
Proof.
  intros.
  induction e; simpl in *; eauto;
    try (f_equal; auto_apply; fast_set_solver!!).
  repeat (case_decide; subst; simpl); try qauto.
  fast_set_solver!!.
Qed.

Lemma subst_ite_distr b e1 e2 x s :
  <{ {x↦s}(ite b e1 e2) }> = <{ ite b ({x↦s}e1) ({x↦s}e2) }>.
Proof.
  destruct b; reflexivity.
Qed.

Lemma subst_id e x :
  {x↦x}e = e.
Proof.
  induction e; simpl; try case_decide; scongruence.
Qed.

Lemma subst_tctx_id (Γ : tctx) x :
  {x↦x} <$> Γ = Γ.
Proof.
  rewrite <- map_fmap_id.
  apply map_fmap_ext.
  scongruence use: subst_id.
Qed.

(** We may prove this one using [subst_open_distr] and [subst_fresh], but a
direct induction gives us a slightly stronger version (without the local closure
constraint). *)
Lemma subst_intro e : forall s x,
  x # e ->
  <{ e^s }> = <{ {x↦s}(e^x) }>.
Proof.
  unfold open. generalize 0.
  induction e; simpl; intros; f_equal;
    (* Case analysis for [EFVar] case *)
    try case_split; subst;
    try auto_apply; fast_set_solver*!.
Qed.

Lemma otval_lc ω :
  otval ω ->
  lc ω.
Proof.
  induction 1; hauto ctrs: lc.
Qed.

Lemma oval_lc v ω :
  oval v ω ->
  lc v /\ lc ω.
Proof.
  induction 1; hauto ctrs: lc use: otval_lc.
Qed.

(** Well-typed and well-kinded expressions are locally closed. *)
Lemma typing_lc Σ Γ e τ :
  Σ; Γ ⊢ e : τ ->
  lc e
with kinding_lc  Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  lc τ.
Proof.
  all: destruct 1; try hauto q: on rew: off ctrs: lc use: oval_lc;
    econstructor; simpl_cofin; qauto.
Qed.

Lemma lc_subst_lc x e s :
  lc s ->
  lc <{ e }> ->
  lc <{ {x↦s}e }>.
Proof.
  intros Hs.
  induction 1; simpl;
    try qauto ctrs: lc;
    econstructor; eauto;
      simpl_cofin?;
      rewrite subst_open_comm in *; eauto; fast_set_solver!!.
Qed.

(* It seems this lemma can reduce to [subst_lc_lc]. But it would require a
side condition on the freshness of [y]. *)
Lemma lc_subst_lc_lc x s t e :
  lc <{ {x↦s}e }> ->
  lc s ->
  lc t ->
  lc <{ {x↦t}e }>.
Proof.
  intros H. intros Hs Ht. remember ({x↦s}e).
  revert dependent e.
  induction H;
    intros []; simpl; inversion 1; subst; simp_hyps;
      try (case_decide; subst); try scongruence;
        econstructor; eauto;
          simpl_cofin?;
          rewrite <- ?subst_open_comm in *; eauto; fast_set_solver!!.
Qed.

Lemma lc_open_atom_lc x e s :
  lc s ->
  lc <{ e^x }> ->
  lc <{ e^s }>.
Proof.
  intros.
  destruct (exist_fresh (fv e)) as [y ?].
  erewrite subst_intro in *; eauto.
  eauto using lc_subst_lc_lc with lc.
Qed.

(** The type of well-typed expression is also locally closed. *)
Lemma typing_kind_lc Σ Γ e τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  lc τ.
Proof.
  intros Hwf.
  induction 1; eauto using kinding_lc with lc;
    try
      lazymatch goal with
      | H : Σ !! _ = Some _ |- _ =>
        apply Hwf in H; simp_hyps; eauto using kinding_lc
      | H : _; _ ⊢ _ : _ |- _ => apply typing_lc in H
      | H : oval _ _ |- _ => apply oval_lc in H
      end;
    qauto use: lc_open_atom_lc inv: lc simp: simpl_cofin?.
Qed.

(** This lemma is equivalent to [SCtx] constructor, but more friendly for
automation. *)
Lemma SCtx_intro {Σ} ℇ e e' E E' :
    Σ ⊨ e -->! e' ->
    ℇ e = E ->
    ℇ e' = E' ->
    ectx ℇ ->
    Σ ⊨ E -->! E'.
Proof.
  hauto ctrs: step.
Qed.

(** ** Theories of free variables *)

Lemma open_fv_l e s :
  fv <{ e^s }> ⊆ fv e ∪ fv s.
Proof.
  unfold open. generalize 0.
  induction e; intros; simpl in *;
    try case_split; fast_set_solver*.
Qed.

Lemma open_fv_r e s :
  fv e ⊆ fv <{ e^s }>.
Proof.
  unfold open. generalize 0.
  induction e; intros; simpl in *;
    fast_set_solver.
Qed.

Lemma open_fresh x e s :
  x # e ->
  x # s ->
  x # <{ e^s }>.
Proof.
  qauto use: open_fv_l solve: set_solver.
Qed.

Lemma open_fresh_atom x e x' :
  x # e ->
  x <> x' ->
  x # <{ e^x' }>.
Proof.
  eauto using open_fresh with set_solver.
Qed.

Ltac induction_map_fold :=
  (* Massage the goal so it is ready for [map_fold_ind]. *)
  match goal with
  | |- context [ map_fold ?f ?b ?m ] =>
    let a := fresh "a" in
    set (map_fold f b m) as a; pattern a, m; subst a
  end;
  apply map_fold_ind.

Lemma tctx_fv_consistent Γ x :
  x ∉ tctx_fv Γ <-> map_Forall (fun _ τ => x # τ) Γ.
Proof.
  unfold tctx_fv.
  split; induction_map_fold;
    qauto use: map_Forall_empty, map_Forall_insert solve: fast_set_solver.
Qed.

Lemma tctx_fv_subseteq Γ τ x :
  Γ !! x = Some τ ->
  fv τ ⊆ tctx_fv Γ.
Proof.
  intros. set_unfold. intros.
  (* Prove by contradiction; alternatively we can prove by [map_fold_ind]. *)
  apply dec_stable.
  hauto use: tctx_fv_consistent.
Qed.

Lemma tctx_fv_insert_subseteq Γ x τ :
  tctx_fv (<[x:=τ]>Γ) ⊆ fv τ ∪ tctx_fv Γ.
Proof.
  intros ? H.
  apply dec_stable. contradict H.
  set_unfold.
  qauto l: on use: tctx_fv_consistent, map_Forall_insert_2.
Qed.

Lemma tctx_fv_insert Γ x τ :
  x ∉ dom aset Γ ->
  tctx_fv (<[x:=τ]>Γ) ≡ fv τ ∪ tctx_fv Γ.
Proof.
  split; intros; try qauto use: tctx_fv_insert_subseteq.
  apply dec_stable.
  set_unfold.
  qauto l: on use: tctx_fv_consistent, map_Forall_insert, not_elem_of_dom.
Qed.

Lemma tctx_stale_inv Γ x :
  x # Γ -> x ∉ dom aset Γ /\ map_Forall (fun _ τ => x # τ) Γ.
Proof.
  hauto use: tctx_fv_consistent solve: fast_set_solver.
Qed.

Lemma subst_tctx_fresh (Γ : tctx) x s :
  x ∉ tctx_fv Γ ->
  {x↦s} <$> Γ = Γ.
Proof.
  intros.
  rewrite <- map_fmap_id.
  apply map_fmap_ext.
  intros; simpl.
  rewrite subst_fresh; eauto.
  hauto use: tctx_fv_consistent solve: fast_set_solver.
Qed.

Lemma otval_closed ω :
  otval ω ->
  closed ω.
Proof.
  induction 1; set_solver.
Qed.

Lemma oval_closed v ω :
  oval v ω ->
  closed ω /\ closed v.
Proof.
  induction 1; qauto use: otval_closed solve: fast_set_solver*.
Qed.

(** Simplifier for free variable reasoning *)

Tactic Notation "fv_rewrite" constr(T) :=
  match T with
  | context [dom aset (<[_:=_]>_)] =>
    rewrite dom_insert
  end.

Tactic Notation "fv_rewrite" constr(T) "in" hyp(H) :=
  match T with
  | context [dom aset (<[_:=_]>_)] =>
    rewrite dom_insert in H
  end.

Tactic Notation "fv_rewrite_l" constr(T) :=
  match T with
  | context [ fv <{ _ ^ _ }> ] =>
    rewrite open_fv_l
  | context [tctx_fv (<[_:=_]>_)] =>
    rewrite tctx_fv_insert_subseteq
  end.

Tactic Notation "fv_rewrite_l" constr(T) "in" hyp(H) :=
  match T with
  | context [ fv <{ _ ^ _ }> ] =>
    rewrite open_fv_l in H
  | context [tctx_fv (<[_:=_]>_)] =>
    rewrite tctx_fv_insert_subseteq in H
  end.

Tactic Notation "fv_rewrite_r" constr(T) :=
  match T with
  | context [ fv <{ _ ^ _ }> ] =>
    rewrite <- open_fv_r
  end.

Tactic Notation "fv_rewrite_r" constr(T) "in" hyp(H) :=
  match T with
  | context [ fv <{ _ ^ _ }> ] =>
    rewrite <- open_fv_r in H
  end.

(* It would be ideal if we check the positivity of the set relation occurrence.
But this works fine and we have to avoid unnecessary setoid rewriting, which is
rather slow when they succeed and extremely slow when they fail. *)
Ltac simpl_fv_rewrite :=
  match goal with
  | |- ?L ⊆ ?R =>
    first [ fv_rewrite (L ⊆ R)
          | fv_rewrite_l L
          | fv_rewrite_r R ]; simpl
  | |- _ ∉ ?T =>
    first [ fv_rewrite T
          | fv_rewrite_l T ]; simpl
  | |- _ ∈ ?T =>
    first [ fv_rewrite T
          | fv_rewrite_r T ]; simpl
  | H : ?L ⊆ ?R |- _ =>
    first [ fv_rewrite_l R in H
          | fv_rewrite_r L in H ]; simpl in H
  | H : _ ∉ ?T |- _ =>
    fv_rewrite_r T in H; simpl in H
  | H : _ ∈ ?T |- _ =>
    fv_rewrite_l T in H; simpl in H
  | H : context [?L ⊆ ?R] |- _ =>
    fv_rewrite (L ⊆ R) in H; simpl in H
  | H : context [_ ∉ ?T] |- _ =>
    fv_rewrite T in H; simpl in H
  | H : context [_ ∈ ?T] |- _ =>
    fv_rewrite T in H; simpl in H
  end.

Tactic Notation "simpl_fv_rewrite_more" "by" tactic3(tac) :=
  match goal with
  | |- context [tctx_fv (<[_:=_]>_)] =>
    rewrite tctx_fv_insert by tac
  | H : context [tctx_fv (<[_:=_]>_)] |- _ =>
    rewrite tctx_fv_insert in H by tac
  end.

(** We thread the saturation-style simplifiers using the [Smpl] plugin, and
then do the rewriting. *)
Smpl Create fv.
Tactic Notation "simpl_fv" :=
  set_fold_not; repeat (smpl fv); clear_blocked; repeat simpl_fv_rewrite.
Tactic Notation "simpl_fv" "*" "by" tactic3(tac) :=
  simpl_fv; repeat simpl_fv_rewrite_more by tac.
Tactic Notation "simpl_fv" "*" :=
  simpl_fv* by fast_set_solver!!.

Ltac simpl_fv_core :=
  match goal with
  | H : oval _ _ |- _ =>
    apply oval_closed in H; unfold closed in H; destruct H
  | H : ?Σ !! _ = Some ?D, Hwf : gctx_wf ?Σ |- _ =>
    lazymatch D with
    (* Handle [DFun] later *)
    | DFun _ _ => fail
    | _ => dup_hyp! H (fun H => apply Hwf in H) with (fun H => try simp_hyp H)
    end
  | H : ?Γ !! _ = Some _ |- _ =>
    lazymatch type of Γ with
    | tctx =>
      dup_hyp! H (fun H => apply elem_of_dom_2 in H);
      dup_hyp! H (fun H => apply tctx_fv_subseteq in H)
    end
  end.
Smpl Add simpl_fv_core : fv.

(** Well-typed and well-kinded terms are closed under typing context. *)
Lemma typing_kinding_fv Σ :
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      fv e ⊆ dom aset Γ) /\
  (forall Γ τ κ,
      Σ; Γ ⊢ τ :: κ ->
      fv τ ⊆ dom aset Γ).
Proof.
  apply typing_kinding_mutind; intros; simpl in *;
    simpl_cofin?; simpl_fv; fast_set_solver*!.
Qed.

Lemma typing_fv Σ Γ e τ :
  Σ; Γ ⊢ e : τ ->
  fv e ⊆ dom aset Γ.
Proof.
  qauto use: typing_kinding_fv.
Qed.

Lemma kinding_fv Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  fv τ ⊆ dom aset Γ.
Proof.
  qauto use: typing_kinding_fv.
Qed.

Ltac simpl_typing_kinding_fv :=
  match goal with
  | H : _; _ ⊢ _ : _ |- _ =>
    dup_hyp! H (fun H => apply typing_fv in H)
  | H : _; _ ⊢ _ :: _ |- _ =>
    dup_hyp! H (fun H => apply kinding_fv in H)
  end.
Smpl Add simpl_typing_kinding_fv : fv.

(** Simplifier given well-formed contexts. *)
Lemma gctx_wf_closed Σ :
  gctx_wf Σ ->
  map_Forall (fun _ D => forall τ e, D = DFun τ e -> closed τ /\ closed e) Σ.
Proof.
  intros Hwf.
  intros ?? H. intros; subst.
  apply Hwf in H. simp_hyps.
  simpl_fv. set_solver.
Qed.

Ltac simpl_wf_fv :=
  match goal with
  | H : ?Σ !! _ = Some (DFun _ _), Hwf : gctx_wf ?Σ |- _ =>
    dup_hyp! H (fun H => apply gctx_wf_closed in H;
                       [ efeed specialize H; [reflexivity |]
                       | apply Hwf])
      with (fun H => unfold closed in H; destruct H)
  end.
Smpl Add simpl_wf_fv : fv.

(** Lemmas about the free variables in the type of a well-typed term. *)
Lemma typing_type_fv Σ Γ e τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  fv τ ⊆ dom aset Γ.
Proof.
  intros Hwf.
  induction 1; intros; simpl in *;
    simpl_cofin?; simpl_fv; fast_set_solver*!.
Qed.

Ltac simpl_typing_type_fv :=
  match goal with
  | H : ?Σ; ?Γ ⊢ _ : _, Hwf : gctx_wf ?Σ |- _ =>
    dup_hyp! H (fun H => apply typing_type_fv in H; [| apply Hwf])
              with (fun H => simpl in H)
  end.
Smpl Add simpl_typing_type_fv : fv.


(** * Metatheories *)

(** ** Properties of [label] *)
(** [label] forms a [SemiLattice].  *)
Instance label_semilattice : SemiLattice label.
Proof.
  split; try reflexivity; repeat intros []; auto.
Qed.

Ltac label_naive_solver :=
  solve [ reflexivity
        | eauto
        | etrans; eauto ].

(** ** Weak head normal form *)
(** We only define weak head normal form for types, but may extend it for other
expressions later. *)
Inductive whnf {Σ : gctx} : expr -> Prop :=
| WUnitT : whnf <{ 𝟙 }>
| WBool : whnf <{ 𝔹 }>
| WOBool : whnf <{ ~𝔹 }>
| WPi τ1 τ2 : whnf <{ Π:τ1, τ2 }>
| WProd τ1 τ2 : whnf <{ τ1 * τ2 }>
| WSum τ1 τ2 : whnf <{ τ1 + τ2 }>
| WOSum τ1 τ2 : whnf <{ τ1 ~+ τ2 }>
| WADT X τ :
    Σ !! X = Some (DADT τ) ->
    whnf <{ gvar X }>
.
Arguments whnf : clear implicits.
Hint Constructors whnf : whnf.

(** Type equivalence for the weak head normal form fragments. This relation
always assumes that the two type arguments are already in [whnf]. *)
Inductive whnf_equiv {Σ : gctx} : expr -> expr -> Prop :=
| WEqUnitT : whnf_equiv <{ 𝟙 }> <{ 𝟙 }>
| WEqBool : whnf_equiv <{ 𝔹 }> <{ 𝔹 }>
| WEqOBool : whnf_equiv <{ ~𝔹 }> <{ ~𝔹 }>
| WEqPi τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ Π:τ1, τ2 }> <{ Π:τ1', τ2' }>
| WEqProd τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 * τ2 }> <{ τ1' * τ2' }>
| WEqSum τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 + τ2 }> <{ τ1' + τ2' }>
| WEqOSum τ1 τ2 τ1' τ2' :
    Σ ⊢ τ1 ≡ τ1' ->
    Σ ⊢ τ2 ≡ τ2' ->
    whnf_equiv <{ τ1 ~+ τ2 }> <{ τ1' ~+ τ2' }>
| WEqADT X : whnf_equiv <{ gvar X }> <{ gvar X }>
.
Arguments whnf_equiv : clear implicits.
Hint Constructors whnf_equiv : whnf_equiv.

Lemma otval_whnf Σ ω :
  otval ω ->
  whnf Σ ω.
Proof.
  induction 1; sfirstorder.
Qed.

(** ** Properties of type equivalence  *)

Ltac equiv_naive_solver :=
  solve [ reflexivity
        | eauto
        | symmetry; eauto
        | etrans; solve [eauto | symmetry; eauto] ].

Instance expr_equiv_is_equiv Σ : Equivalence (expr_equiv Σ).
Proof.
Admitted.

(** [whnf_equiv] is a faithful fragment of [expr_equiv]. *)
Lemma expr_equiv_iff_whnf_equiv Σ τ1 τ2 :
  whnf Σ τ1 -> whnf Σ τ2 ->
  Σ ⊢ τ1 ≡ τ2 <->
  whnf_equiv Σ τ1 τ2.
Proof.
Admitted.

(* NOTE: Be aware of circular proofs! In case we need [gctx_wf] as a side
condition, as we need this lemma to prove [gctx_wf] for well-typed global
context. *)
Lemma expr_equiv_weakening Σ τ τ' :
  Σ ⊢ τ ≡ τ' ->
  forall Σ', Σ ⊆ Σ' ->
        Σ' ⊢ τ ≡ τ'.
Admitted.

(* Some side conditions may be needed for the next few lemmas. *)

Lemma expr_equiv_step Σ e e' :
  Σ ⊨ e -->! e' ->
  Σ ⊢ e ≡ e'.
Proof.
Admitted.

Lemma expr_equiv_subst Σ τ τ' e e' x :
  Σ ⊢ τ ≡ τ' ->
  Σ ⊢ e ≡ e' ->
  Σ ⊢ {x↦e}τ ≡ {x↦e'}τ'.
Proof.
Admitted.

Lemma expr_equiv_open_atom Σ τ1 τ2 x :
  Σ ⊢ τ1 ≡ τ2 ->
  Σ ⊢ τ1^x ≡ τ2^x.
Proof.
Admitted.

(* We may weaken it so Γ = ∅. But we need to weaken all theorems depending on
it. *)
Lemma expr_equiv_obliv_type_preserve_ Σ Γ τ τ' κ κ' :
  gctx_wf Σ ->
  Σ; Γ ⊢ τ :: κ ->
  Σ; Γ ⊢ τ' :: κ' ->
  Σ ⊢ τ ≡ τ' ->
  κ ⊑ <{ *@O }> ->
  Σ; Γ ⊢ τ' :: *@O.
Proof.
Admitted.

Lemma expr_equiv_obliv_type_preserve Σ Γ τ τ' κ :
  gctx_wf Σ ->
  Σ; Γ ⊢ τ :: *@O ->
  Σ ⊢ τ ≡ τ' ->
  Σ; Γ ⊢ τ' :: κ ->
  Σ; Γ ⊢ τ' :: *@O.
Proof.
  qauto use: expr_equiv_obliv_type_preserve_ solve: label_naive_solver.
Qed.

Lemma expr_equiv_rename Σ τ τ' x y :
  Σ ⊢ τ ≡ τ' ->
  Σ ⊢ {x↦y}τ ≡ {x↦y}τ'.
Proof.
  qauto use: expr_equiv_subst solve: equiv_naive_solver.
Qed.

Lemma expr_equiv_subst1 Σ τ τ' x s :
  Σ ⊢ τ ≡ τ' ->
  Σ ⊢ {x↦s}τ ≡ {x↦s}τ'.
Proof.
  qauto use: expr_equiv_subst solve: equiv_naive_solver.
Qed.

Lemma expr_equiv_subst2 Σ τ x e e' :
  Σ ⊢ e ≡ e' ->
  Σ ⊢ {x↦e}τ ≡ {x↦e'}τ.
Proof.
  qauto use: expr_equiv_subst solve: equiv_naive_solver.
Qed.

Lemma expr_equiv_open1 Σ τ1 τ2 e :
  Σ ⊢ τ1 ≡ τ2 ->
  Σ ⊢ τ1^e ≡ τ2^e.
Proof.
  destruct (exist_fresh (fv τ1 ∪ fv τ2)) as [x ?].
  erewrite (subst_intro τ1 e x) by fast_set_solver!!.
  erewrite (subst_intro τ2 e x) by fast_set_solver!!.
  eauto using expr_equiv_subst1, expr_equiv_open_atom.
Qed.

Lemma expr_equiv_open2 Σ τ e1 e2 :
  Σ ⊢ e1 ≡ e2 ->
  Σ ⊢ τ^e1 ≡ τ^e2.
Proof.
  destruct (exist_fresh (fv τ)) as [x ?].
  erewrite (subst_intro τ e1 x) by eassumption.
  erewrite (subst_intro τ e2 x) by eassumption.
  eauto using expr_equiv_subst2.
Qed.

(** Simplify type equivalence to [whnf_equiv]. Possibly derive contradiction if
two equivalent types in [whnf] have different head. *)
Tactic Notation "simpl_whnf_equiv" "by" tactic3(tac) :=
  match goal with
  | H : _ ⊢ ?τ1 ≡ ?τ2 |- _ =>
    apply expr_equiv_iff_whnf_equiv in H;
    [ sinvert H
    | solve [tac]
    | solve [tac] ]
  end.

Tactic Notation "simpl_whnf_equiv" :=
  simpl_whnf_equiv by eauto using otval_whnf with whnf.

(** ** Kind inversion  *)
Tactic Notation "kind_inv_solver" "by" tactic3(tac) :=
  match goal with
  | |- _; _ ⊢ ?τ :: _ -> _ => remember τ
  end;
  induction 1; subst; simp_hyps; try scongruence;
  tac.

Tactic Notation "kind_inv_solver" :=
  kind_inv_solver by (repeat esplit; eauto; label_naive_solver).

Lemma kind_inv_pi Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ Π:τ1, τ2 :: κ ->
  κ = <{ *@M }> /\
  exists L l1 l2,
    (∀ x, x ∉ L → Σ; (<[x:=τ1]> Γ) ⊢ τ2^x :: *@l2) /\
    Σ; Γ ⊢ τ1 :: *@l1.
Proof.
  kind_inv_solver by sfirstorder use: top_inv.
Qed.

Lemma kind_inv_bool Σ Γ κ :
  Σ; Γ ⊢ 𝔹 :: κ -> <{ *@P }> ⊑ κ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_prod Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ τ1 * τ2 :: κ ->
  exists l,
    Σ; Γ ⊢ τ1 :: *@l /\
    Σ; Γ ⊢ τ2 :: *@l /\
    <{ *@l }> ⊑ κ.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sum Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ τ1 + τ2 :: κ ->
  <{ *@P }> ⊑ κ /\
  exists l,
    Σ; Γ ⊢ τ1 :: *@l /\
    Σ; Γ ⊢ τ2 :: *@l.
Proof.
  kind_inv_solver by qauto l: on solve: label_naive_solver
                           use: join_ub_r.
Qed.

Lemma kind_inv_osum Σ Γ τ1 τ2 κ :
  Σ; Γ ⊢ τ1 ~+ τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  Σ; Γ ⊢ τ1 :: *@O /\
  Σ; Γ ⊢ τ2 :: *@O.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_gvar Σ Γ X κ :
  Σ; Γ ⊢ gvar X :: κ ->
  <{ *@P }> ⊑ κ /\ exists τ, Σ !! X = Some (DADT τ).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_app Σ Γ e1 e2 κ :
  Σ; Γ ⊢ e1 e2 :: κ ->
  <{ *@O }> ⊑ κ /\
  exists X τ e',
    Σ !! X = Some (DOADT τ e') /\
    Σ; Γ ⊢ e2 : τ /\
    e1 = <{ gvar X }>.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ite Σ Γ e0 τ1 τ2 κ :
  Σ; Γ ⊢ if e0 then τ1 else τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  Σ; Γ ⊢ e0 : 𝔹 /\
  Σ; Γ ⊢ τ1 :: *@O /\
  Σ; Γ ⊢ τ2 :: *@O.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_let Σ Γ e τ κ :
  Σ; Γ ⊢ let e in τ :: κ ->
  <{ *@O }> ⊑ κ /\
  exists τ' L,
    Σ; Γ ⊢ e : τ' /\
    (forall x, x ∉ L -> Σ; (<[x:=τ']> Γ) ⊢ τ^x :: *@O).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_case Σ Γ e0 τ1 τ2 κ :
  Σ; Γ ⊢ case e0 of τ1 | τ2 :: κ ->
  <{ *@O }> ⊑ κ /\
  exists τ1' τ2' L1 L2,
    Σ; Γ ⊢ e0 : τ1' + τ2' /\
    (forall x, x ∉ L1 -> Σ; (<[x:=τ1']> Γ) ⊢ τ1^x :: *@O) /\
    (forall x, x ∉ L2 -> Σ; (<[x:=τ2']> Γ) ⊢ τ2^x :: *@O).
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_mux Σ Γ e0 e1 e2 κ :
  Σ; Γ ⊢ mux e0 e1 e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_sec Σ Γ e κ :
  Σ; Γ ⊢ s𝔹 e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ret Σ Γ e κ :
  Σ; Γ ⊢ r𝔹 e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_pair Σ Γ e1 e2 κ :
  Σ; Γ ⊢ (e1, e2) :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_proj Σ Γ b e κ :
  Σ; Γ ⊢ π@b e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_inj Σ Γ b τ e κ :
  Σ; Γ ⊢ inj@b<τ> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_oinj Σ Γ b τ e κ :
  Σ; Γ ⊢ ~inj@b<τ> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_ocase Σ Γ e0 e1 e2 κ :
  Σ; Γ ⊢ ~case e0 of e1 | e2 :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_fold Σ Γ X e κ :
  Σ; Γ ⊢ fold<X> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Lemma kind_inv_unfold Σ Γ X e κ :
  Σ; Γ ⊢ unfold<X> e :: κ -> False.
Proof.
  kind_inv_solver.
Qed.

Tactic Notation "apply_kind_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _ ⊢ Π:_, _ :: _ => tac kind_inv_pi
  | _; _ ⊢ 𝔹 :: _ => tac kind_inv_bool
  | _; _ ⊢ _ _ :: _ => tac kind_inv_app
  | _; _ ⊢ let _ in _ :: _ => tac kind_inv_let
  | _; _ ⊢ _ * _ :: _ => tac kind_inv_prod
  | _; _ ⊢ _ + _ :: _ => tac kind_inv_sum
  | _; _ ⊢ _ ~+ _ :: _ => tac kind_inv_osum
  | _; _ ⊢ gvar _ :: _ => tac kind_inv_gvar
  | _; _ ⊢ if _ then _ else _ :: _ => tac kind_inv_ite
  | _; _ ⊢ case _ of _ | _ :: _ => tac kind_inv_case
  | _; _ ⊢ mux _ _ _ :: _ => apply kind_inv_mux in H; elim H
  | _; _ ⊢ s𝔹 _ :: _ => apply kind_inv_sec in H; elim H
  | _; _ ⊢ r𝔹 _ :: _ => apply kind_inv_ret in H; elim H
  | _; _ ⊢ (_, _) :: _ => apply kind_inv_pair in H; elim H
  | _; _ ⊢ π@_ _ :: _ => apply kind_inv_proj in H; elim H
  | _; _ ⊢ inj@_<_> _ :: _ => apply kind_inv_inj in H; elim H
  | _; _ ⊢ ~inj@_<_> _ :: _ => apply kind_inv_oinj in H; elim H
  | _; _ ⊢ ~case _ of _ | _ :: _ => apply kind_inv_ocase in H; elim H
  | _; _ ⊢ fold<_> _ :: _ => apply kind_inv_fold in H; elim H
  | _; _ ⊢ unfold<_> _ :: _ => apply kind_inv_unfold in H; elim H
  end.

Tactic Notation "apply_kind_inv" hyp(H) :=
  apply_kind_inv H by (fun lem => apply lem in H; try simp_hyp H).

Tactic Notation "apply_kind_inv" :=
  do_hyps (fun H => try apply_kind_inv H).

Tactic Notation "apply_kind_inv" "*" :=
  do_hyps (fun H => try dup_hyp H (fun H => apply_kind_inv H)).

(** ** Type inversion *)
Tactic Notation "type_inv_solver" "by" tactic3(tac) :=
  match goal with
  | |- _; _ ⊢ ?e : _ -> _ => remember e
  end;
  induction 1; subst; simp_hyps; try scongruence;
  tac.

Tactic Notation "type_inv_solver" :=
  type_inv_solver by (repeat esplit; eauto; equiv_naive_solver).

Lemma type_inv_unit Σ Γ τ :
  Σ; Γ ⊢ () : τ ->
  Σ ⊢ τ ≡ 𝟙.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_lit Σ Γ b τ :
  Σ; Γ ⊢ lit b : τ ->
  Σ ⊢ τ ≡ 𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_abs Σ Γ e τ2 τ :
  Σ; Γ ⊢ \:τ2 => e : τ ->
  exists τ1 l L,
    Σ; Γ ⊢ τ2 :: *@l /\
    (forall x, x ∉ L -> Σ; (<[x:=τ2]> Γ) ⊢ e^x : τ1^x) /\
    Σ ⊢ τ ≡ Π:τ2, τ1.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_gvar Σ Γ x τ :
  Σ; Γ ⊢ gvar x : τ ->
  exists τ' e,
    Σ !! x = Some (DFun τ' e) /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_pair Σ Γ e1 e2 τ :
  Σ; Γ ⊢ (e1, e2) : τ ->
  exists τ1 τ2,
    Σ; Γ ⊢ e1 : τ1 /\
    Σ; Γ ⊢ e2 : τ2 /\
    Σ ⊢ τ ≡ τ1 * τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_inj Σ Γ b e τ' τ :
  Σ; Γ ⊢ inj@b<τ'> e : τ ->
  exists τ1 τ2,
    τ' = <{ τ1 + τ2 }> /\
    Σ; Γ ⊢ τ1 + τ2 :: *@P /\
    Σ; Γ ⊢ e : ite b τ1 τ2 /\
    Σ ⊢ τ ≡ τ1 + τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_oinj Σ Γ b e τ' τ :
  Σ; Γ ⊢ ~inj@b<τ'> e : τ ->
  exists τ1 τ2,
    τ' = <{ τ1 ~+ τ2 }> /\
    Σ; Γ ⊢ τ1 ~+ τ2 :: *@O /\
    Σ; Γ ⊢ e : ite b τ1 τ2 /\
    Σ ⊢ τ ≡ τ1 ~+ τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_fold Σ Γ X e τ :
  Σ; Γ ⊢ fold<X> e : τ ->
  exists τ',
    Σ; Γ ⊢ e : τ' /\
    Σ !! X = Some (DADT τ') /\
    Σ ⊢ τ ≡ gvar X.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_boxedlit Σ Γ b τ :
  Σ; Γ ⊢ [b] : τ ->
  Σ ⊢ τ ≡ ~𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_boxedinj Σ Γ b v ω τ :
  Σ; Γ ⊢ [inj@b<ω> v] : τ ->
  exists ω1 ω2,
    ω = <{ ω1 ~+ ω2 }> /\
    oval <{ [inj@b<ω> v] }> ω /\
    Σ ⊢ τ ≡ ω1 ~+ ω2.
Proof.
  type_inv_solver by hauto lq: on solve: equiv_naive_solver
                           ctrs: oval inv: oval.
Qed.

Lemma type_inv_ocase Σ Γ e0 e1 e2 τ :
  Σ; Γ ⊢ ~case e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' L1 L2,
    Σ; Γ ⊢ τ' :: *@O /\
    Σ; Γ ⊢ e0 : τ1 ~+ τ2 /\
    (forall x, x ∉ L1 -> Σ; (<[x:=τ1]> Γ) ⊢ e1^x : τ') /\
    (forall x, x ∉ L2 -> Σ; (<[x:=τ2]> Γ) ⊢ e2^x : τ') /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_prod Σ Γ τ1 τ2 τ :
  Σ; Γ ⊢ τ1 * τ2 : τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_osum Σ Γ τ1 τ2 τ :
  Σ; Γ ⊢ τ1 ~+ τ2 : τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_app Σ Γ e1 e2 τ :
  Σ; Γ ⊢ e1 e2 : τ ->
  exists τ1 τ2,
    Σ; Γ ⊢ e1 : Π:τ2, τ1 /\
    Σ; Γ ⊢ e2 : τ2 /\
    Σ ⊢ τ ≡ τ1^e2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_let Σ Γ e1 e2 τ :
  Σ; Γ ⊢ let e1 in e2 : τ ->
  exists τ1 τ2 L,
    Σ; Γ ⊢ e1 : τ1 /\
    (forall x, x ∉ L -> Σ; (<[x:=τ1]> Γ) ⊢ e2^x : τ2^x) /\
    Σ ⊢ τ ≡ τ2^e1.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_sec Σ Γ e τ :
  Σ; Γ ⊢ s𝔹 e : τ ->
  Σ; Γ ⊢ e : 𝔹 /\
  Σ ⊢ τ ≡ ~𝔹.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_ret Σ Γ e τ :
  Σ; Γ ⊢ r𝔹 e : τ -> False.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_ite Σ Γ e0 e1 e2 τ :
  Σ; Γ ⊢ if e0 then e1 else e2 : τ ->
  exists τ',
    Σ; Γ ⊢ e0 : 𝔹 /\
    Σ; Γ ⊢ e1 : τ' /\
    Σ; Γ ⊢ e2 : τ' /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_mux Σ Γ e0 e1 e2 τ :
  Σ; Γ ⊢ mux e0 e1 e2 : τ ->
  exists τ',
    Σ; Γ ⊢ e0 : ~𝔹 /\
    Σ; Γ ⊢ e1 : τ' /\
    Σ; Γ ⊢ e2 : τ' /\
    Σ; Γ ⊢ τ' :: *@O /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_proj Σ Γ b e τ :
  Σ; Γ ⊢ π@b e : τ ->
  exists τ1 τ2,
    Σ; Γ ⊢ e : τ1 * τ2 /\
    Σ ⊢ τ ≡ ite b τ1 τ2.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_case Σ Γ e0 e1 e2 τ :
  Σ; Γ ⊢ case e0 of e1 | e2 : τ ->
  exists τ1 τ2 τ' κ L1 L2,
    Σ; Γ ⊢ τ' :: κ /\
    Σ; Γ ⊢ e0 : τ1 + τ2 /\
    (forall x, x ∉ L1 -> Σ; (<[x:=τ1]> Γ) ⊢ e1^x : τ') /\
    (forall x, x ∉ L2 -> Σ; (<[x:=τ2]> Γ) ⊢ e2^x : τ') /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Lemma type_inv_unfold Σ Γ X e τ :
  Σ; Γ ⊢ unfold<X> e : τ ->
  exists τ',
    Σ !! X = Some (DADT τ') /\
    Σ; Γ ⊢ e : gvar X /\
    Σ ⊢ τ ≡ τ'.
Proof.
  type_inv_solver.
Qed.

Tactic Notation "apply_type_inv" hyp(H) "by" tactic3(tac) :=
  lazymatch type of H with
  | _; _ ⊢ () : _ => tac type_inv_unit
  | _; _ ⊢ lit _ : _ => tac type_inv_lit
  | _; _ ⊢ gvar _ : _ => tac type_inv_gvar
  | _; _ ⊢ \:_ => _ : _ => tac type_inv_abs
  | _; _ ⊢ _ _ : _ => tac type_inv_app
  | _; _ ⊢ let _ in _ : _ => tac type_inv_let
  | _; _ ⊢ (_, _) : _ => tac type_inv_pair
  | _; _ ⊢ s𝔹 _ : _ => tac type_inv_sec
  | _; _ ⊢ r𝔹 _ : _ => apply type_inv_ret in H; elim H
  | _; _ ⊢ π@_ _ : _ => tac type_inv_proj
  | _; _ ⊢ inj@_<_> _ : _ => tac type_inv_inj
  | _; _ ⊢ ~inj@_<_> _ : _ => tac type_inv_oinj
  | _; _ ⊢ if _ then _ else _ : _ => tac type_inv_ite
  | _; _ ⊢ mux _ _ _ : _ => tac type_inv_mux
  | _; _ ⊢ case _ of _ | _ : _ => tac type_inv_case
  | _; _ ⊢ ~case _ of _ | _ : _ => tac type_inv_ocase
  | _; _ ⊢ fold<_> _ : _ => tac type_inv_fold
  | _; _ ⊢ unfold<_> _ : _ => tac type_inv_unfold
  | _; _ ⊢ [_] : _ => tac type_inv_boxedlit
  | _; _ ⊢ [inj@_<_> _] : _ => tac type_inv_boxedinj
  | _; _ ⊢ _ * _ : _ => apply type_inv_prod in H; elim H
  | _; _ ⊢ _ ~+ _ : _ => apply type_inv_osum in H; elim H
  end.

Tactic Notation "apply_type_inv" hyp(H) :=
  apply_type_inv H by (fun lem => apply lem in H; try simp_hyp H).

Tactic Notation "apply_type_inv" :=
  do_hyps (fun H => try apply_type_inv H).

Tactic Notation "apply_type_inv" "*" :=
  do_hyps (fun H => try dup_hyp H (fun H => apply_type_inv H)).

(** ** Properties of [expr_wf] *)

Lemma open_expr_wf e s :
  expr_wf e ->
  expr_wf s ->
  expr_wf <{ e^s }>.
Proof.
  unfold open. intros H. generalize 0.
  induction H; simpl; intros; try case_decide; eauto with expr_wf.
Qed.

Lemma open_expr_wf_inv e s :
  expr_wf <{ e^s }> ->
  expr_wf s ->
  expr_wf e.
Proof.
  unfold open. generalize 0.
  induction e; simpl; intros; qauto l: on inv: expr_wf ctrs: expr_wf.
Qed.

Lemma open_atom_expr_wf_inv e x :
  expr_wf <{ e^x }> ->
  expr_wf e.
Proof.
  qauto use: open_expr_wf_inv ctrs: expr_wf.
Qed.

Lemma typing_expr_wf Σ Γ e τ :
  Σ; Γ ⊢ e : τ ->
  expr_wf e
with kinding_expr_wf Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  expr_wf τ.
Proof.
  all: destruct 1; eauto with expr_wf;
    simpl_cofin?; qauto l: on ctrs: expr_wf use: open_atom_expr_wf_inv.
Qed.

Lemma otval_well_kinded ω Σ Γ :
  otval ω ->
  Σ; Γ ⊢ ω :: *@O.
Proof.
  induction 1; hauto lq: on ctrs: kinding solve: label_naive_solver.
Qed.

Lemma otval_uniq Σ ω1 ω2 :
  otval ω1 ->
  otval ω2 ->
  Σ ⊢ ω1 ≡ ω2 ->
  ω1 = ω2.
Proof.
  intros H. revert ω2.
  induction H; intros; simpl_whnf_equiv;
    qauto l:on rew:off inv: otval.
Qed.

Lemma oval_elim v ω :
  oval v ω ->
  val v /\ otval ω /\ ∅; ∅ ⊢ v : ω.
Proof.
  intros H. use H.
  induction H; hauto lq:on ctrs: val, otval, typing.
Qed.

Lemma oval_intro v ω Σ Γ :
  val v ->
  otval ω ->
  Σ; Γ ⊢ v : ω ->
  oval v ω.
Proof.
  intros H. revert ω.
  induction H; inversion 1; intros; subst;
    apply_type_inv;
    simpl_whnf_equiv;
    try hauto lq: on rew: off
              ctrs: oval, typing
              use: otval_well_kinded
              solve: equiv_naive_solver.

  (* Case [inj@_<_> _] *)
  repeat match goal with
         | H : _ ⊢ ?ω1 ≡ ?ω2 |- _ =>
           apply otval_uniq in H; try qauto l: on inv: otval
         end.
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

(** ** Canonical forms *)
Ltac canonical_form_solver :=
  inversion 1; intros; subst; eauto;
  apply_type_inv;
  apply_kind_inv;
  simpl_whnf_equiv.

Lemma canonical_form_abs Σ Γ e τ2 τ1 :
  val e ->
  Σ; Γ ⊢ e : Π:τ2, τ1 ->
  exists e' τ, e = <{ \:τ => e' }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_bool Σ Γ e :
  val e ->
  Σ; Γ ⊢ e : 𝔹 ->
  exists b, e = <{ b }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_obool Σ Γ e :
  val e ->
  Σ; Γ ⊢ e : ~𝔹 ->
  exists b, e = <{ [b] }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_prod Σ Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 * τ2 ->
  exists v1 v2, val v1 /\ val v2 /\ e = <{ (v1, v2) }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_sum Σ Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 + τ2 ->
  exists b v τ, val v /\ e = <{ inj@b<τ> v }>.
Proof.
  canonical_form_solver.
Qed.

Lemma canonical_form_osum Σ Γ e τ1 τ2 :
  val e ->
  Σ; Γ ⊢ e : τ1 ~+ τ2 ->
  exists b v ω1 ω2, val v /\ otval ω1 /\ otval ω2 /\
               e = <{ [inj@b<ω1 ~+ ω2> v] }>.
Proof.
  canonical_form_solver;
    (* The cases when [e] is boxed injection. *)
    select (otval _) (fun H => sinvert H);
    repeat esplit; auto.
Qed.

(** Though it seems we should have a condition of [X] being an (public) ADT, this
condition is not needed since it is implied by the typing judgment. *)
Lemma canonical_form_fold Σ Γ e X :
  val e ->
  Σ; Γ ⊢ e : gvar X ->
  exists v X', val v /\ e = <{ fold<X'> v }>.
Proof.
  inversion 1; inversion 1; intros; subst; eauto;
  apply_type_inv;
  apply_kind_inv;
  simpl_whnf_equiv.
Qed.

(** ** Properties of kinding  *)
Lemma any_kind_otval Σ Γ τ :
  Σ; Γ ⊢ τ :: *@A ->
  otval τ.
Proof.
  remember <{ *@A }>.
  induction 1; subst; try hauto ctrs: otval.
  - srewrite join_bot_iff. easy.
  - eauto using bot_inv.
Qed.

(** ** Progress *)

(** Take a step through evaluation context. *)
Ltac step_ectx_solver :=
  match goal with
  | H : _ ⊨ _ -->! _ |- exists _, _ ⊨ _ -->! _ =>
    eexists;
    eapply SCtx_intro;
    [ solve [apply H]
    | higher_order_reflexivity
    | higher_order_reflexivity
    | solve [constructor; eauto] ]
  end.

(** The combined progress theorems for expressions and types. *)
Theorem progress_ Σ :
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
  apply typing_kinding_mutind; intros; subst;
    (* If a type is not used in the conclusion, the mutual inductive hypothesis
    for it is useless. Remove this hypothesis to avoid slowdown the
    automation. *)
    try match goal with
        | H : context [otval ?τ \/ _] |- val ?e \/ _ =>
          assert_fails contains e τ; clear H
        end;
    (* Try solve the boring cases, unless they are the trickier ones. *)
    first [ goal_is (val <{ ~case _ of _ | _ }> \/ _)
          | goal_is (otval <{ _ + _ }> \/ _)
          | match goal with
            | |- otval ?τ \/ _ => is_var τ
            end
          (* Take care of the simple cases. *)
          | goal_is (val <{ [inj@_<_> _] }> \/ _); sfirstorder use: oval_elim
          | qauto q: on rew: off
                  simp: simpl_map
                  ctrs: val, otval, step, ectx
          (* Take care of the more complex cases involving evaluation context. *)
          (* For expression progress. *)
          | goal_contains val;
            qauto q: on
                  ctrs: val, step
                  solve: step_ectx_solver
                  use: canonical_form_abs,
                       canonical_form_bool,
                       canonical_form_obool,
                       canonical_form_prod,
                       canonical_form_sum,
                       canonical_form_fold
          (* For oblivious type progress. *)
          | goal_contains otval;
            qauto q: on
                  ctrs: otval, step
                  solve: step_ectx_solver
                  use: canonical_form_bool,
                       canonical_form_sum
          | idtac ].

  (* [~case _ of _ | _] *)
  - right. intuition.
    (* Discriminee is value. *)
    + select (_; _ ⊢ _ : _) (fun H => apply canonical_form_osum in H); eauto.
      simp_hyps.
      select! (otval _) (fun H => use (oval_inhabited _ H)).
      hauto ctrs: step.
    (* Discriminee can take a step. *)
    + hauto solve: step_ectx_solver ctrs: step.

  (* [_ + _]. This case is impossible. *)
  - enough (<{ *@P }> ⊑ <{ *@O }>) by easy.
    scongruence unfold: kind use: join_ub_r.

  (* Kinding subsumption *)
  - select kind (fun κ => destruct κ); sintuition use: any_kind_otval.
Qed.

Theorem progress Σ τ e :
  Σ; ∅ ⊢ e : τ ->
  val e \/ exists e', Σ ⊨ e -->! e'.
Proof.
  hauto use: progress_.
Qed.

(** ** Weakening lemmas  *)
Lemma weakening_ Σ :
  (forall Γ e τ,
    Σ; Γ ⊢ e : τ ->
    forall Σ' Γ',
      Σ ⊆ Σ' ->
      Γ ⊆ Γ' ->
      Σ'; Γ' ⊢ e : τ) /\
  (forall Γ τ κ,
    Σ; Γ ⊢ τ :: κ ->
    forall Σ' Γ',
      Σ ⊆ Σ' ->
      Γ ⊆ Γ' ->
      Σ'; Γ' ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind; intros; subst;
    try qauto l: on use: insert_mono, expr_equiv_weakening
              ctrs: typing, kinding;
    try qauto l: on use: lookup_weaken
              ctrs: typing, kinding;
    (* For the [case]/[~case] cases *)
    econstructor; eauto using insert_mono.
Qed.

Lemma weakening Σ Γ Σ' Γ' e τ :
  Σ; Γ ⊢ e : τ ->
  Σ ⊆ Σ' ->
  Γ ⊆ Γ' ->
  Σ'; Γ' ⊢ e : τ.
Proof.
  hauto use: weakening_.
Qed.

Lemma kinding_weakening Σ Γ Σ' Γ' τ κ :
  Σ; Γ ⊢ τ :: κ ->
  Σ ⊆ Σ' ->
  Γ ⊆ Γ' ->
  Σ'; Γ' ⊢ τ :: κ.
Proof.
  hauto use: weakening_.
Qed.

Lemma weakening_empty Σ Γ e τ :
  Σ; ∅ ⊢ e : τ ->
  Σ; Γ ⊢ e : τ.
Proof.
  eauto using weakening, map_empty_subseteq.
Qed.

Lemma kinding_weakening_empty Σ Γ τ κ :
  Σ; ∅ ⊢ τ :: κ ->
  Σ; Γ ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, map_empty_subseteq.
Qed.

Lemma weakening_insert Σ Γ e τ τ' x :
  Σ; Γ ⊢ e : τ ->
  x ∉ dom aset Γ ->
  Σ; (<[x:=τ']>Γ) ⊢ e : τ.
Proof.
  eauto using weakening, insert_fresh_subseteq.
Qed.

Lemma kinding_weakening_insert Σ Γ τ τ' κ x :
  Σ; Γ ⊢ τ :: κ ->
  x ∉ dom aset Γ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, insert_fresh_subseteq.
Qed.

(** ** Well-formedness of [gctx] *)

Lemma gdef_typing_wf D Σ' Σ :
  Σ' =[ D ]=> Σ ->
  gctx_wf Σ' ->
  gctx_wf Σ.
Proof.
  inversion 1; subst; intros Hd X' D Hm.
  all:
    destruct (decide (X' = X)); subst; simpl_map;
    [ inversion Hm; subst
    | apply Hd in Hm; case_split; simp_hyps ];
    eauto 10 using weakening, kinding_weakening, insert_subseteq.
Qed.

Lemma gdefs_typing_wf_ Ds Σ' Σ :
  Σ' ={ Ds }=> Σ ->
  gctx_wf Σ' ->
  gctx_wf Σ.
Proof.
  induction 1; eauto using gdef_typing_wf.
Qed.

Lemma gdefs_typing_wf Ds Σ :
  ∅ ={ Ds }=> Σ ->
  gctx_wf Σ.
Proof.
  intros. eapply gdefs_typing_wf_; eauto.
  unfold gctx_wf, map_Forall.
  intros. simplify_map_eq.
Qed.

(** ** Renaming lemmas *)

(* Warning: this lemma is rather slow. *)
Lemma typing_kinding_rename_ Σ x y τ' :
  gctx_wf Σ ->
  (forall Γ' e τ,
      Σ; Γ' ⊢ e : τ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        y ∉ {[x]} ∪ fv e ∪ fv τ' ∪ dom aset Γ ->
        Σ; (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}e : {x↦y}τ) /\
  (forall Γ' τ κ,
      Σ; Γ' ⊢ τ :: κ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        y ∉ {[x]} ∪ fv τ ∪ fv τ' ∪ dom aset Γ ->
        Σ; (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}τ :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    (* First we normalize the typing and kinding judgments so they are ready
    for applying typing and kinding rules to. *)
    rewrite ?subst_open_distr by constructor;
    rewrite ?subst_ite_distr;
    try lazymatch goal with
        | |- _; _ ⊢ [inj@_< ?ω > _] : {_↦_}?ω =>
          rewrite subst_fresh by shelve
        | |- context [decide (_ = _)] =>
          case_decide; subst
        end;
      (* Apply typing and kinding rules. *)
      econstructor;
      simpl_cofin?;
      (* We define this subroutine [go] for applying induction hypotheses. *)
      let go Γ :=
          (* We massage the typing and kinding judgments so that we can apply
          induction hypotheses to them. *)
          rewrite <- ?subst_ite_distr;
            rewrite <- ?subst_open_comm by (try constructor; shelve);
            try lazymatch Γ with
                | <[_:=_]>(<[_:=_]>({_↦_} <$> _)) =>
                  first [ rewrite <- fmap_insert
                        (* We may have to apply commutativity first. *)
                        | rewrite insert_commute by shelve;
                          rewrite <- fmap_insert ]
                end;
            (* Apply one of the induction hypotheses. *)
            auto_apply in
      (* Make sure we complete handling the typing and kinding judgments first.
      Otherwise some existential variables may have undesirable
      instantiation. *)
      lazymatch goal with
      | |- _; ?Γ ⊢ _ : _ => go Γ
      | |- _; ?Γ ⊢ _ :: _ => go Γ
      | _ => idtac
      end;
        (* Try to solve other side conditions. *)
        eauto;
        repeat lazymatch goal with
               | |- _ ∉ _ =>
                 shelve
               | |- _ <> _ =>
                 shelve
               | |- <[_:=_]>(<[_:=_]>_) = <[_:=_]>(<[_:=_]>_) =>
                 apply insert_commute
               | |- _ ⊢ _ ≡ _ =>
                 apply expr_equiv_rename
               | |- <[?y:=_]>_ !! ?y = Some _ =>
                 simplify_map_eq
               | |- <[_:=_]>_ !! _ = Some _ =>
                 rewrite lookup_insert_ne; [simplify_map_eq |]
               | |- Some _ = Some _ =>
                 try reflexivity; repeat f_equal
               | |- _ = {_↦_} _ =>
                 rewrite subst_fresh
               | H : ?Σ !! ?x = Some _ |- ?Σ !! ?x = Some _ =>
                 rewrite H
               end;
        eauto.

  Unshelve.

  all : try fast_set_solver!!; simpl_fv; fast_set_solver*!!.
Qed.

(** We also allow [x=y]. *)
Lemma typing_rename_ Σ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e : τ ->
  x ∉ fv τ' ∪ dom aset Γ ->
  y ∉ fv e ∪ fv τ' ∪ dom aset Γ ->
  Σ; (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}e : {x↦y}τ.
Proof.
  intros.
  destruct (decide (y = x)); subst.
  - scongruence use: subst_id, subst_tctx_id.
  - qauto use: typing_kinding_rename_ solve: fast_set_solver!!.
Qed.

Lemma kinding_rename_ Σ Γ τ τ' κ x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ :: κ ->
  x ∉ fv τ' ∪ dom aset Γ ->
  y ∉ fv τ ∪ fv τ' ∪ dom aset Γ ->
  Σ; (<[y:=τ']>({x↦y} <$> Γ)) ⊢ {x↦y}τ :: κ.
Proof.
  intros.
  destruct (decide (y = x)); subst.
  - scongruence use: subst_id, subst_tctx_id.
  - qauto use: typing_kinding_rename_ solve: fast_set_solver!!.
Qed.

(** The actual renaming lemmas. The side conditions are slightly different than
the general version. *)
Lemma typing_rename Σ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  y ∉ fv τ' ∪ fv e ∪ dom aset Γ ->
  Σ; (<[y:=τ']>Γ) ⊢ e^y : τ^y.
Proof.
  intros.
  destruct (decide (y = x)); subst; eauto.
  rewrite <- (subst_tctx_fresh Γ x y) by fast_set_solver!!.
  rewrite (subst_intro e y x) by fast_set_solver!!.
  rewrite (subst_intro τ y x) by fast_set_solver!!.
  apply typing_rename_; eauto.
  fast_set_solver!!.
  simpl_fv. fast_set_solver!!.
Qed.

Lemma kinding_rename Σ Γ τ κ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ^x :: κ ->
  x ∉ fv τ' ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  y ∉ fv τ' ∪ fv τ ∪ dom aset Γ ->
  Σ; (<[y:=τ']>Γ) ⊢ τ^y :: κ.
Proof.
  intros.
  destruct (decide (y = x)); subst; eauto.
  rewrite <- (subst_tctx_fresh Γ x y) by fast_set_solver!!.
  rewrite (subst_intro τ y x) by fast_set_solver!!.
  apply kinding_rename_; eauto.
  fast_set_solver!!.
  simpl_fv. fast_set_solver!!.
Qed.

Lemma typing_rename_lc Σ Γ e τ τ' x y :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  y ∉ fv τ' ∪ fv e ∪ dom aset Γ ->
  Σ; (<[y:=τ']>Γ) ⊢ e^y : τ.
Proof.
  intros Hwf H. intros.
  erewrite <- (open_lc_intro τ y) by eauto using typing_kind_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_kind_lc.
  eapply typing_rename; eauto.
Qed.

(** ** Admissible typing and kinding introduction rules *)
Section typing_kinding_intro.

  #[local]
  Set Warnings "-notation-overridden,-parsing".

  Context {Σ : gctx} (Hwf : gctx_wf Σ).
  Notation "Γ '⊢' e ':' τ" := (Σ; Γ ⊢ e : τ)
                                (at level 40,
                                 e custom oadt at level 99,
                                 τ custom oadt at level 99).
  Notation "Γ '⊢' τ '::' κ" := (Σ; Γ ⊢ τ :: κ)
                                 (at level 40,
                                  τ custom oadt at level 99,
                                  κ custom oadt at level 99).

  Ltac typing_intro_solver :=
    intros; econstructor; eauto; simpl_cofin?;
    lazymatch goal with
    | |- _ ⊢ _ : _^_ => eapply typing_rename
    | |- _ ⊢ _ : _ => eapply typing_rename_lc
    | |- _ ⊢ _ :: _ => eapply kinding_rename
    end; eauto;
    try fast_set_solver!!; simpl_fv; fast_set_solver!!.

  Lemma TAbs_intro Γ e τ1 τ2 l x :
    <[x:=τ2]>Γ ⊢ e^x : τ1^x ->
    Γ ⊢ τ2 :: *@l ->
    x ∉ fv e ∪ fv τ1 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ \:τ2 => e : (Π:τ2, τ1).
  Proof.
    typing_intro_solver.
  Qed.

  Lemma TLet_intro Γ e1 e2 τ1 τ2 x :
    <[x:=τ1]>Γ ⊢ e2^x : τ2^x ->
    Γ ⊢ e1 : τ1 ->
    x ∉ fv e2 ∪ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ let e1 in e2 : τ2^e1.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma TCase_intro Γ e0 e1 e2 τ1 τ2 τ κ x :
    <[x:=τ1]>Γ ⊢ e1^x : τ ->
    <[x:=τ2]>Γ ⊢ e2^x : τ ->
    Γ ⊢ e0 : τ1 + τ2 ->
    Γ ⊢ τ :: κ ->
    x ∉ fv e1 ∪ fv e2 ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ case e0 of e1 | e2 : τ.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma TOCase_intro Γ e0 e1 e2 τ1 τ2 τ x :
    <[x:=τ1]>Γ ⊢ e1^x : τ ->
    <[x:=τ2]>Γ ⊢ e2^x : τ ->
    Γ ⊢ e0 : τ1 ~+ τ2 ->
    Γ ⊢ τ :: *@O ->
    x ∉ fv e1 ∪ fv e2 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ ~case e0 of e1 | e2 : τ.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KPi_intro Γ τ1 τ2 l1 l2 x :
    <[x:=τ1]>Γ ⊢ τ2^x :: *@l2 ->
    Γ ⊢ τ1 :: *@l1 ->
    x ∉ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ (Π:τ1, τ2) :: *@M.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KCase_intro Γ e0 τ1 τ2 τ1' τ2' x :
    <[x:=τ1']>Γ ⊢ τ1^x :: *@O ->
    <[x:=τ2']>Γ ⊢ τ2^x :: *@O ->
    Γ ⊢ e0 : τ1' + τ2' ->
    x ∉ fv τ1 ∪ fv τ2 ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ case e0 of τ1 | τ2 :: *@O.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KLet_intro Γ e τ τ' x :
    <[x:=τ']>Γ ⊢ τ^x :: *@O ->
    Γ ⊢ e : τ' ->
    x ∉ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
    Γ ⊢ let e in τ :: *@O.
  Proof.
    typing_intro_solver.
  Qed.

  Lemma KProd_intro Γ τ1 τ2 l1 l2 :
    Γ ⊢ τ1 :: *@l1 ->
    Γ ⊢ τ2 :: *@l2 ->
    Γ ⊢ τ1 * τ2 :: *@(l1 ⊔ l2).
  Proof.
    eauto using join_ub_l, join_ub_r with kinding.
  Qed.

End typing_kinding_intro.

(** Tactics for apply typing/kinding rules. Similar to [econstructor], but it
uses the admissible rules. It also fails rather than applying [TConv]
blindly. *)
(* NOTE: it would be great if [econstructor] can apply all but some
constructors. *)
Ltac typing_intro_ Σ T :=
  lazymatch T with
  | Σ; _ ⊢ fvar _ : _ => eapply TFVar
  | Σ; _ ⊢ gvar _ : _ => eapply TGVar
  | Σ; _ ⊢ \:_ => _ : _ => eapply TAbs_intro
  | Σ; _ ⊢ let _ in _ : _ => eapply TLet_intro
  | Σ; _ ⊢ _ _ : _ => eapply TApp
  | Σ; _ ⊢ () : _ => eapply TUnit
  | Σ; _ ⊢ lit _ : _ => eapply TLit
  | Σ; _ ⊢ s𝔹 _ : _ => eapply TSec
  | Σ; _ ⊢ (_, _) : _ => eapply TPair
  | Σ; _ ⊢ mux _ _ _ : _ => eapply TMux
  | Σ; _ ⊢ π@_ _ : _ => eapply TProj
  | Σ; _ ⊢ inj@_<_> _ : _ => eapply TInj
  | Σ; _ ⊢ ~inj@_<_> _ : _ => eapply TOInj
  | Σ; _ ⊢ ~case _ of _ | _ : _ => eapply TOCase_intro
  | Σ; _ ⊢ fold<_> _ : _ => eapply TFold
  | Σ; _ ⊢ unfold<_> _ : _ => eapply TUnfold
  | Σ; _ ⊢ if _ then _ else _ : _ => eapply TIte
  | Σ; _ ⊢ case _ of _ | _ : _ => eapply TCase_intro
  | Σ; _ ⊢ [_] : _ => eapply TBoxedLit
  | Σ; _ ⊢ [inj@_<_> _] : _ => eapply TBoxedInj
  | Σ; _ ⊢ ?e : ?τ => is_var e; assert_fails (is_evar τ); eapply TConv
  end.

Ltac kinding_intro_ Σ T :=
  lazymatch T with
  | Σ; _ ⊢ gvar _ :: _ => eapply KVarADT
  | Σ; _ ⊢ 𝟙 :: _ => eapply KUnit
  | Σ; _ ⊢ 𝔹 :: _ => eapply KBool
  | Σ; _ ⊢ ~𝔹 :: _ => eapply KOBool
  | Σ; _ ⊢ Π:_, _ :: _ => eapply KPi_intro
  | Σ; _ ⊢ (gvar _) _ :: _ => eapply KApp
  | Σ; _ ⊢ _ * _ :: _ => eapply KProd_intro
  | Σ; _ ⊢ _ + _ :: _ => eapply KSum
  | Σ; _ ⊢ _ ~+ _ :: _ => eapply KOSum
  | Σ; _ ⊢ if _ then _ else _ :: _ => eapply KIte
  | Σ; _ ⊢ case _ of _ | _ :: _ => eapply KCase_intro
  | Σ; _ ⊢ let _ in _ :: _ => eapply KLet_intro
  | Σ; _ ⊢ ?τ :: _ => is_var τ; eapply KSub
  end.

Tactic Notation "typing_kinding_intro_" tactic3(tac) :=
  match goal with
  | H : gctx_wf ?Σ |- ?T =>
    tac Σ T;
    try match goal with
        | |- gctx_wf Σ => apply H
        end
  end.

Tactic Notation "typing_intro" :=
  typing_kinding_intro_ (fun Σ T => typing_intro_ Σ T).

Tactic Notation "kinding_intro" :=
  typing_kinding_intro_ (fun Σ T => kinding_intro_ Σ T).

Tactic Notation "typing_kinding_intro" :=
  lazymatch goal with
  | |- _; _ ⊢ _ : _ => typing_intro
  | |- _; _ ⊢ _ :: _ => kinding_intro
  end.

(** ** Substitution lemma *)

Lemma subst_tctx_typing_kinding_ Σ x s :
  gctx_wf Σ ->
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      x ∉ fv τ ∪ dom aset Γ ->
      Σ; ({x↦s} <$> Γ) ⊢ e : τ) /\
  (forall Γ τ κ,
      Σ; Γ ⊢ τ :: κ ->
      x ∉ dom aset Γ ->
      Σ; ({x↦s} <$> Γ) ⊢ τ :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    econstructor; eauto;
      simpl_cofin?;
      (* Try to apply induction hypotheses. *)
      lazymatch goal with
      | |- _; ?Γ ⊢ ?e : ?τ =>
        auto_apply || lazymatch goal with
                      | H : _ -> _; ?Γ' ⊢ e : τ |- _ =>
                        replace Γ with Γ'; [auto_apply |]
                      end
      | |- _; ?Γ ⊢ ?τ :: _ =>
        auto_apply || lazymatch goal with
                      | H : _ -> _; ?Γ' ⊢ τ :: _ |- _ =>
                        replace Γ with Γ'; [auto_apply |]
                      end
      | _ => idtac
      end; eauto;
        (* Solve other side conditions *)
        repeat lazymatch goal with
               | |- _ ∉ _ =>
                 shelve
               | |- _ <> _ =>
                 shelve
               | |- {_↦_} <$> (<[_:=_]>_) = <[_:=_]>({_↦_} <$> _) =>
                 rewrite fmap_insert; try reflexivity; repeat f_equal
               | |- _ !! _ = Some _ =>
                 simplify_map_eq
               | |- Some _ = Some _ =>
                 try reflexivity; repeat f_equal
               | |- {_↦_} _ = _ =>
                 rewrite subst_fresh
               end;
        eauto.

  Unshelve.

  all : try fast_set_solver!!; simpl_fv; fast_set_solver!!.
Qed.

Lemma subst_tctx_typing Σ Γ e τ x s :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  x ∉ fv τ ∪ dom aset Γ ->
  Σ; ({x↦s} <$> Γ) ⊢ e : τ.
Proof.
  qauto use: subst_tctx_typing_kinding_.
Qed.

(* Note that [lc s] is not needed, and it is here only for convenience. I will
drop it in the actual lemma. *)
Lemma subst_preservation_ Σ x s τ' :
  gctx_wf Σ ->
  lc s ->
  (forall Γ' e τ,
      Σ; Γ' ⊢ e : τ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        Σ; Γ ⊢ s : τ' ->
        Σ; ({x↦s} <$> Γ) ⊢ {x↦s}e : {x↦s}τ) /\
  (forall Γ' τ κ,
      Σ; Γ' ⊢ τ :: κ ->
      forall Γ,
        Γ' = <[x:=τ']>Γ ->
        x ∉ fv τ' ∪ dom aset Γ ->
        Σ; Γ ⊢ s : τ' ->
        Σ; ({x↦s} <$> Γ) ⊢ {x↦s}τ :: κ).
Proof.
  intros Hwf Hlc.
  apply typing_kinding_mutind; intros; subst; simpl in *;
    (* First we normalize the typing and kinding judgments so they are ready
    for applying typing and kinding rules to. *)
    rewrite ?subst_open_distr by assumption;
    rewrite ?subst_ite_distr;
    try lazymatch goal with
        | |- _; _ ⊢ [inj@_< ?ω > _] : {_↦_}?ω =>
          rewrite subst_fresh by shelve
        | |- context [decide (_ = _)] =>
          (* The case of [fvar x] is the trickier one. Let's handle it later. *)
          case_decide; subst; [shelve |]
        end;
      (* Apply typing and kinding rules. *)
      econstructor;
      simpl_cofin?;
      (* We define this subroutine [go] for applying induction hypotheses. *)
      let go Γ :=
          (* We massage the typing and kinding judgments so that we can apply
          induction hypotheses to them. *)
          rewrite <- ?subst_ite_distr;
            rewrite <- ?subst_open_comm by (try assumption; shelve);
            try lazymatch Γ with
                | <[_:=_]>({_↦_} <$> _) =>
                  rewrite <- fmap_insert
                end;
            (* Apply one of the induction hypotheses. *)
            auto_eapply in
      (* Make sure we complete handling the typing and kinding judgments first.
      Otherwise some existential variables may have undesirable
      instantiation. *)
      lazymatch goal with
      | |- _; ?Γ ⊢ _ : _ => go Γ
      | |- _; ?Γ ⊢ _ :: _ => go Γ
      | _ => idtac
      end;
        (* Try to solve other side conditions. *)
        eauto;
        repeat lazymatch goal with
               | |- _ ∉ _ =>
                 shelve
               | |- _ <> _ =>
                 shelve
               | |- <[_:=_]>(<[_:=_]>_) = <[_:=_]>(<[_:=_]>_) =>
                 apply insert_commute
               | |- _ ⊢ _ ≡ _ =>
                 apply expr_equiv_subst1
               | |- (_ <$> _) !! _ = Some _ =>
                 simplify_map_eq
               | |- _; (<[_:=_]>_) ⊢ _ : _ =>
                 apply weakening_insert
               | |- Some _ = Some _ =>
                 try reflexivity; repeat f_equal
               | |- _ = {_↦_} _ =>
                 rewrite subst_fresh
               | H : ?Σ !! ?x = Some _ |- ?Σ !! ?x = Some _ =>
                 rewrite H
               end;
        eauto.
  Unshelve.

  (* Case [fvar x] *)
  simplify_map_eq.
  rewrite subst_fresh.
  apply subst_tctx_typing; eauto.

  (* Solve other side conditions of free variables. *)
  all : try fast_set_solver!!; simpl_fv; fast_set_solver*!!.
Qed.

(** The actual substitution lemma *)
Lemma subst_preservation Σ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e : τ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ {x↦s}e : {x↦s}τ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  eapply subst_preservation_; eauto using typing_lc.
  fast_set_solver!!.
Qed.

Lemma kinding_subst_preservation Σ x s τ' Γ τ κ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ :: κ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ {x↦s}τ :: κ.
Proof.
  intros.
  rewrite <- (subst_tctx_fresh Γ x s) by fast_set_solver!!.
  eapply subst_preservation_; eauto using typing_lc.
  fast_set_solver!!.
Qed.

Lemma open_preservation Σ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ^x ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ e^s : τ^s.
Proof.
  intros.
  rewrite (subst_intro e s x) by fast_set_solver!!.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma kinding_open_preservation Σ x s τ' Γ τ κ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ^x :: κ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ τ^s :: κ.
Proof.
  intros.
  rewrite (subst_intro τ s x) by fast_set_solver!!.
  eapply kinding_subst_preservation; eauto.
  fast_set_solver!!.
Qed.

Lemma open_preservation_lc Σ x s τ' Γ e τ :
  gctx_wf Σ ->
  Σ; (<[x:=τ']>Γ) ⊢ e^x : τ ->
  Σ; Γ ⊢ s : τ' ->
  x ∉ fv τ' ∪ fv e ∪ fv τ ∪ dom aset Γ ∪ tctx_fv Γ ->
  Σ; Γ ⊢ e^s : τ.
Proof.
  intros Hwf H. intros.
  erewrite <- (open_lc_intro τ s) by eauto using typing_kind_lc.
  erewrite <- (open_lc_intro τ x) in H by eauto using typing_kind_lc.
  eapply open_preservation; eauto.
Qed.

(** Types of well-typed expressions are well-kinded *)
Lemma type_well_kinded Σ Γ e τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  exists κ, Σ; Γ ⊢ τ :: κ.
Proof.
  intros Hwf.
  induction 1; simp_hyps; eauto with kinding;
    try match goal with
        | H : _ !! _ = _ |- _ =>
          apply Hwf in H; simp_hyps; eauto using kinding_weakening_empty
        end;
    apply_kind_inv; simpl_cofin?; simp_hyps;
    try first [ eexists; typing_kinding_intro; eauto; fast_set_solver!!
              (* Types may be opened. *)
              | eexists; qauto use: kinding_open_preservation
                               solve: fast_set_solver!! ].

  (* Boxed injection case *)
  sfirstorder use: otval_well_kinded, oval_elim.
Qed.

(** Oblivious type can not be typed. *)
Lemma obliv_type_not_typed Σ X τ e Γ τ' :
  Σ !! X = Some (DOADT τ e) ->
  Σ; Γ ⊢ gvar X : τ' ->
  False.
Proof.
  intros.
  apply_type_inv.
  scongruence.
Qed.

(** ** Preservation *)

Ltac case_ite_expr :=
  lazymatch goal with
  | |- _; _ ⊢ ?e : _ =>
    lazymatch e with
    | context [<{ ite ?b _ _ }>] => destruct b
    end
  | |- _; _ ⊢ ?τ :: _ =>
    lazymatch τ with
    | context [<{ ite ?b _ _ }>] => destruct b
    end
  end.

(** The combined preservation theorems for expressions and types. *)
Theorem preservation_ Σ :
  gctx_wf Σ ->
  (forall Γ e τ,
      Σ; Γ ⊢ e : τ ->
      forall e', Σ ⊨ e -->! e' ->
            Σ; Γ ⊢ e' : τ) /\
  (forall Γ τ κ,
      Σ; Γ ⊢ τ :: κ ->
      forall τ', Σ ⊨ τ -->! τ' ->
            Σ; Γ ⊢ τ' :: κ).
Proof.
  intros Hwf.
  apply typing_kinding_mutind; intros; subst;
    (* Repeatedly perform inversion on [step], but only if we know how to step
    it (i.e. the initial expression has a constructor for its head). *)
    repeat
      (lazymatch goal with
       | H : _ ⊨ ?e -->! _ |- _ =>
         head_constructor e;
         (* Try to apply induction hypotheses to the [step] relation first
         before we invert and remove it. *)
         try match goal with
             | H' : _ -> forall _, _ ⊨ e -->! _ -> _ |- _ =>
               dup_hyp H (fun H => apply H' in H);
               (* Discharge the side condition for the kinding induction
               hypotheses. *)
               [ clear H' | label_naive_solver ]
             | H' : forall _, _ ⊨ e -->! _ -> _ |- _ =>
               dup_hyp H (fun H => apply H' in H);
               clear H'
             end;
         sinvert H
       end;
       (* Try to do inversion on the evaluation contexts. *)
       try select (ectx _) (fun H => sinvert H);
       simplify_eq);
    (* Try to simplify and solve some cases involving global context. *)
    try match goal with
        | H : _ !! ?X = Some (DOADT _ _), H' : _; _ ⊢ gvar ?X : _ |- _ =>
          (* It is not possible to type oblivious type *)
          exfalso; eauto using obliv_type_not_typed
        | Hwf : gctx_wf ?Σ, H : ?Σ !! _ = Some _ |- _ =>
          dup_hyp H (fun H => apply Hwf in H; simp_hyp H);
            try hauto use: weakening_empty
        end;
    (* Try to solve the easy cases. *)
    try solve [ try case_ite_expr;
                simp_hyps;
                repeat
                  (eauto;
                   lazymatch goal with
                   | |- _; _ ⊢ _ : ?τ =>
                     first [ is_evar τ | econstructor ]
                   | |- _; _ ⊢ _ :: ?κ =>
                     first [ is_evar κ | econstructor ]
                   end) ];
    (* Take care of the more interesting cases. *)
    simpl_cofin?;
    (* Derive well-kindedness from typing. *)
    try select! (_; _ ⊢ _ : _)
          (fun H => dup_hyp H (fun H => eapply type_well_kinded in H;
                                    [ simp_hyp H | eauto ]));
    (* Apply inversion lemmas for typing and kinding. *)
    apply_type_inv*;
    apply_kind_inv*;
    (* Derive equivalence for the sub-expressions. *)
    try simpl_whnf_equiv;
    (* We may have cofinite quantifiers that are generated by the inversion
    lemmas. *)
    simpl_cofin?;
    simplify_eq;
    (* Repeatedly apply substitution (open) preservation lemmas and typing
    rules. *)
    repeat
      (try case_ite_expr;
       eauto;
       match goal with
       | H : _; (<[_:=_]>?Γ) ⊢ ?e^_ : ?τ^_ |- _; ?Γ ⊢ ?e^_ : ?τ^_ =>
         eapply open_preservation
       | H : _; (<[_:=_]>?Γ) ⊢ ?e^_ : ?τ |- _; ?Γ ⊢ ?e^_ : ?τ =>
         eapply open_preservation_lc
       | H : _; (<[_:=_]>?Γ) ⊢ ?e^_ : _ |- _; ?Γ ⊢ ?e^_ : ?τ =>
         is_evar τ; eapply open_preservation
       | H : _; (<[_:=_]>?Γ) ⊢ ?τ^_ :: _ |- _; ?Γ ⊢ ?τ^_ :: _ =>
         eapply kinding_open_preservation
       | |- _; _ ⊢ _ : ?τ =>
         tryif is_evar τ
         then typing_intro
         else first [ typing_intro | eapply TConv ]
       | |- _ ⊢ ?τ ≡ _ =>
         tryif (head_constructor τ)
         then apply expr_equiv_iff_whnf_equiv; econstructor
         else qauto l: on rew: off
                    solve: equiv_naive_solver
                    use: expr_equiv_step, expr_equiv_open1, expr_equiv_open2
       | |- _ ∉ _ => fast_set_solver!!
       end).

  (* The case when oblivious injection steps to boxed injection [SOInj]. *)
  hauto lq: on ctrs: oval inv: otval use: oval_intro.

  (* These 4 cases are generated by the case when oblivious case analysis
  steps to [mux]: [SOCase]. *)
  1-4:
  repeat
    match goal with
    | H : oval ?e _ |- _ =>
      head_constructor e; sinvert H
    end;
    select! (oval _ _) (fun H => apply oval_elim in H; simp_hyp H);
    eapply TConv;
    [ eauto using weakening, map_empty_subseteq
    | eauto
    | equiv_naive_solver].

  (* The case when we apply oblivious type to its argument : [SAppOADT] *)
  eapply kinding_open_preservation; eauto.
  - eapply kinding_weakening; eauto.
    rewrite insert_union_singleton_l.
    apply map_union_subseteq_l.
  - fast_set_solver!!.
Qed.

Theorem preservation Σ Γ e e' τ :
  gctx_wf Σ ->
  Σ; Γ ⊢ e : τ ->
  Σ ⊨ e -->! e' ->
  Σ; Γ ⊢ e' : τ.
Proof.
  hauto use: preservation_.
Qed.

(** ** Soundness *)

Definition stuck (Σ : gctx) (e : expr) : Prop :=
  nf (@step Σ) e /\ ¬val e.

Corollary soundness Ds e Σ τ e' :
  program_typing Ds e Σ τ ->
  Σ ⊨ e -->* e' ->
  ¬(stuck Σ e').
Proof.
  intros [Hd Ht]. apply gdefs_typing_wf in Hd.
  induction 1;
    qauto use: progress, preservation unfold: stuck, nf.
Qed.

End lang.

End oadt.
