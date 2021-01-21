From oadt Require Import prelude.

(** The core language for oblivious algebraic data type. *)

Module oadt.

Section lang.

Context `{is_atom : Atom atom amap aset}.
Implicit Types (x X : atom) (L : aset).

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
| EBoxedOInj (b : bool) (τ e : expr)
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
Coercion EGVar : atom >-> expr.

Declare Scope oadt_scope.
Delimit Scope oadt_scope with oadt.

Declare Custom Entry oadt.
Notation "<{ e }>" := e (e custom oadt at level 99).
Notation "( x )" := x (in custom oadt, x at level 99).
Notation "x" := x (in custom oadt at level 0, x constr at level 0).
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
Notation "[ 'inj@' b < τ > e ]" := (EBoxedOInj b τ e)
                                      (in custom oadt at level 0,
                                          b constr at level 0,
                                          τ custom oadt at level 0,
                                          e custom oadt at level 0,
                                          format "[ inj@ b < τ >  e ]").
Notation "[ 'inl' < τ > e ]" := (EBoxedOInj true τ e)
                                   (in custom oadt at level 0,
                                       τ custom oadt at level 0,
                                       e custom oadt at level 0,
                                       format "[ inl < τ >  e ]").
Notation "[ 'inr' < τ > e ]" := (EBoxedOInj false τ e)
                                   (in custom oadt at level 0,
                                       τ custom oadt at level 0,
                                       e custom oadt at level 0,
                                       format "[ inr < τ >  e ]").

Declare Custom Entry oadt_def.
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
  | EBVar n => if decide (k = n) then s else e
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

Definition open s t := open_ 0 s t.

Notation "t ^ s" := (open s t) (in custom oadt at level 20).

(** ** Polynomial algebraic data type (α) *)
Inductive padt : expr -> Prop :=
| PUnitT : padt <{ 𝟙 }>
| PBool : padt <{ 𝔹 }>
| PProd α1 α2 : padt α1 -> padt α2 -> padt <{ α1 * α2 }>
| PSum α1 α2 : padt α1 -> padt α2 -> padt <{ α1 + α2 }>
| PGVar (X : atom) : padt X
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
| VLit (b : bool) : val <{ b }>
| VPair v1 v2 : val v1 -> val v2 -> val <{ (v1, v2) }>
| VAbs τ e : val <{ \:τ => e }>
| VInj b τ v : val v -> val <{ inj@b<τ> v }>
| VFold X v : val v -> val <{ fold<X> v }>
| VBoxedLit (b : bool) : val <{ [b] }>
| VBoxedOInj b ω v : otval ω -> val v -> val <{ [inj@b<ω> v] }>
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
| OVOSum (b : bool) v ω1 ω2 :
    oval v (if b then ω1 else ω2) ->
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
| SCtx ℇ e e' :
    ectx ℇ ->
    e -->! e' ->
    ℇ e -->! ℇ e'
| SApp τ e v :
    val v ->
    <{ (\:τ => e) v }> -->! <{ e^v }>
| SLet v e :
    val v ->
    <{ let v in e }> -->! <{ e^v }>
| SCase b τ v e1 e2 :
    val v ->
    <{ case inj@b<τ> v of e1 | e2 }> -->! if b then <{ e1^v }> else <{ e2^v }>
| SOCase b ω1 ω2 v e1 e2 v1 v2 :
    otval ω1 -> otval ω2 -> val v ->
    oval v1 ω1 -> oval v2 ω2 ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
      EMux <{ [b] }> (if b then <{ e1^v }> else <{ e1^v1 }>)
                     (if b then <{ e2^v2 }> else <{ e2^v }>)
| SAppOADT X τ e v :
    Σ !! X = Some (DOADT τ e) ->
    <{ X v }> -->! <{ e^v }>
| SAppFun x τ e :
    Σ !! x = Some (DFun τ e) ->
    <{ x }> -->! <{ e }>
| SOInj b ω v :
    otval ω -> val v ->
    <{ ~inj@b<ω> v }> -->! <{ [inj@b<ω> v] }>
| SIte (b : bool) e1 e2 :
    <{ if b then e1 else e2 }> -->! if b then e1 else e2
(** If we also want runtime obliviousness (e.g., against malicious adversaries),
we can check [v1] and [v2] are oblivious values in this rule. *)
| SMux b v1 v2 :
    val v1 -> val v2 ->
    <{ mux [b] v1 v2 }> -->! if b then v1 else v2
| SProj b v1 v2 :
    val v1 -> val v2 ->
    <{ π@b (v1, v2) }> -->! if b then v1 else v2
| SFold X X' v :
    val v ->
    <{ unfold<X> (fold <X'> v) }> -->! v
| SSec (b : bool) :
    <{ s𝔹 b }> -->! <{ [b] }>
(** Delimited release [b] *)
| SRet (b : bool) :
    <{ r𝔹 [b] }> -->! b

where "e '-->!' e'" := (step e e').
Notation "Σ '⊢' e '-->!' e'" := (@step Σ e e') (at level 40).
Hint Constructors step : step.

(** * Typing *)

(** ** Security level labels (l) *)
Variant label :=
| LAny
| LPublic
| LSecure
| LMixed
.

Declare Custom Entry oadt_label.
Notation "'A'" := (LAny) (in custom oadt_label at level 0).
Notation "'P'" := (LPublic) (in custom oadt_label at level 0).
Notation "'S'" := (LSecure) (in custom oadt_label at level 0).
Notation "'M'" := (LMixed) (in custom oadt_label at level 0).

(** ** Kinds (κ) *)
Variant kind :=
| KProper (l : label)
| KOADT (τ : expr)
.
Declare Custom Entry oadt_kind.
Notation "* @ l" := (KProper l) (in custom oadt_kind at level 0,
                                    l custom oadt_label at level 0,
                                    format "* @ l").
Notation "τ '=>' *" := (KOADT τ) (in custom oadt_kind at level 0,
                                     τ custom oadt at level 99).

(** ** Typing context (Γ) *)
Notation tctx := (amap expr).

(** ** Expression typing *)


(** * Infrastructure *)

(** ** Locally closed *)
Inductive lc : expr -> Prop :=
| LCFVar x : lc (EFVar x)
| LCGVar x : lc (EGVar x)
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
| LCLit b : lc (ELit b)
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
| LCBoxedOInj b τ e : lc τ -> lc e -> lc <{ [inj@b<τ> e] }>
.
Hint Constructors lc : lc.

(** ** Substitution (for local free variables) *)
Reserved Notation "'{' s '/' x '}' e" (in custom oadt at level 20, x constr).
Fixpoint subst (x : atom) (s : expr) (e : expr) : expr :=
  match e with
  | EFVar y => if decide (x = y) then s else e
  (** Congruence rules *)
  | <{ Π:τ1, τ2 }> => <{ Π:{s/x}τ1, {s/x}τ2 }>
  | <{ \:τ => e }> => <{ \:{s/x}τ => {s/x}e }>
  | <{ let e1 in e2 }> => <{ let {s/x}e1 in {s/x}e2 }>
  | <{ case e0 of e1 | e2 }> => <{ case {s/x}e0 of {s/x}e1 | {s/x}e2 }>
  | <{ ~case e0 of e1 | e2 }> => <{ ~case {s/x}e0 of {s/x}e1 | {s/x}e2 }>
  | <{ τ1 * τ2 }> => <{ ({s/x}τ1) * ({s/x}τ2) }>
  | <{ τ1 + τ2 }> => <{ ({s/x}τ1) + ({s/x}τ2) }>
  | <{ τ1 ~+ τ2 }> => <{ ({s/x}τ1) ~+ ({s/x}τ2) }>
  | <{ e1 e2 }> => <{ ({s/x}e1) ({s/x}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({s/x}e) }>
  | <{ r𝔹 e }> => <{ r𝔹 ({s/x}e) }>
  | <{ if e0 then e1 else e2 }> => <{ if {s/x}e0 then {s/x}e1 else {s/x}e2 }>
  | <{ mux e0 e1 e2 }> => <{ mux ({s/x}e0) ({s/x}e1) ({s/x}e2) }>
  | <{ (e1, e2) }> => <{ ({s/x}e1, {s/x}e2) }>
  | <{ π@b e }> => <{ π@b ({s/x}e) }>
  | <{ inj@b<τ> e }> => <{ inj@b<({s/x}τ)> ({s/x}e) }>
  | <{ ~inj@b<τ> e }> => <{ ~inj@b<({s/x}τ)> ({s/x}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({s/x}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({s/x}e) }>
  | _ => e
  end

where "'{' s '/' x '}' e" := (subst x s e) (in custom oadt).

(** * Metatheories *)

End lang.

End oadt.
