From oadt Require Import prelude.

(** The core language for oblivious algebraic data type. *)

Module oadt.

Section lang.

(* TODO: module type and parameters may be a better way to parameterize [name]
and [nmap]. *)

(** [name] is the type for names, with decidable equality. *)
Context {name : Set} `{EqDecision name}.

(** [nmap A] is a finite, partial map from [name] to [A]. *)
Context {nmap : Type -> Type} `{FinMap name nmap}.

(** * Syntax *)

(** ** Expressions (e, τ) *)
Inductive expr :=
| EUnitT
| EBool
| EOBool
| EProd (τ1 τ2 : expr)
| ESum (τ1 τ2 : expr)
| EOSum (τ1 τ2 : expr)
| EPi (x : name) (τ1 τ2: expr)
| EVar (x : name)
| EApp (e1 e2 : expr)
| EUnitV
| ELit (b : bool)
| ESec (e : expr)
| ERet (e : expr)
| EIte (e0 e1 e2 : expr)
| EMux (e0 e1 e2 : expr)
| EPair (e1 e2 : expr)
| ELetP (x1 x2 : name) (e1 e2 : expr)
| EInj (b : bool) (τ e : expr)
| ECase (e0 : expr) (x1 : name) (e1 : expr) (x2 : name) (e2 : expr)
| EOInj (b : bool) (τ e : expr)
| EOCase (e0 : expr) (x1 : name) (e1 : expr) (x2 : name) (e2 : expr)
| EAbs (x : name) (τ e : expr)
| ELet (x : name) (e1 e2 : expr)
| EFold (X : name) (e : expr)
| EUnfold (X : name) (e : expr)
(** Runtime expressions *)
| EBoxedLit (b : bool)
| EBoxedOInj (b : bool) (τ e : expr)
.

(** ** GLobal named definitions (D) *)
Variant gdef :=
| DADT (X : name) (e : expr)
| DOADT (Y : name) (x : name) (τ e : expr)
| DFun (x : name) (τ e : expr)
.

(** ** Programs (P) *)
(* TODO: may define [program] as [list gdef * expr]. *)
Definition program := list gdef.

(** ** Global context (Σ) *)
(** It is used in operational semantics and typing. *)
Definition gctx := nmap gdef.

(** ** Notations *)
(* Adapted from Software Foundations. *)
Coercion ELit : bool >-> expr.
Coercion EVar : name >-> expr.

(* TODO: allow them to be used outside of this section. *)
Declare Scope oadt_scope.
Delimit Scope oadt_scope with oadt.
Declare Custom Entry oadt.
Notation "<{ e }>" := e (e custom oadt at level 99).
Notation "( x )" := x (in custom oadt, x at level 99).
Notation "x" := x (in custom oadt at level 0, x constr at level 0).
Notation "! x" := (EVar x) (in custom oadt at level 0).
Notation "' b" := (ELit b) (in custom oadt at level 0).
Notation "'𝟙'" := EUnitT (in custom oadt at level 0).
Notation "'Unit'" := EUnitT (in custom oadt at level 0).
Notation "'𝔹'" := EBool (in custom oadt at level 0).
Notation "'Bool'" := EBool (in custom oadt at level 0).
Notation "'~𝔹'" := EOBool (in custom oadt at level 0).
Notation "'~Bool'" := EOBool (in custom oadt at level 0).
Notation "t1 * t2" := (EProd t1 t2) (in custom oadt at level 2,
                                        t1 custom oadt,
                                        t2 custom oadt at level 0).
Notation "t1 + t2" := (ESum t1 t2) (in custom oadt at level 3,
                                       left associativity).
Notation "t1 ~+ t2" := (EOSum t1 t2) (in custom oadt at level 3,
                                         left associativity).
Notation "'Π' x : t1 , t2" := (EPi x t1 t2) (in custom oadt at level 50,
                                                right associativity).
Notation "e1 e2" := (EApp e1 e2) (in custom oadt at level 1, left associativity).
Notation "()" := EUnitV (in custom oadt at level 0).
Notation "( x , y , .. , z )" := (EPair .. (EPair x y) .. z)
                                   (in custom oadt at level 0,
                                       x custom oadt at level 99,
                                       y custom oadt at level 99,
                                       z custom oadt at level 99).
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
Notation "'let' ( x , y ) '=' e1 'in' e2" := (ELetP x y e1 e2)
                                               (in custom oadt at level 0,
                                                   x custom oadt at level 99,
                                                   y custom oadt at level 99,
                                                   e1 custom oadt at level 99,
                                                   e2 custom oadt at level 99).
Notation "'let' x '=' e1 'in' e2" := (ELet x e1 e2)
                                       (in custom oadt at level 0,
                                           x custom oadt at level 99,
                                           e1 custom oadt at level 99,
                                           e2 custom oadt at level 99).
Notation "'inj@' b < t > e" := (EInj b t e) (in custom oadt at level 0,
                                                b custom oadt at level 0,
                                                t custom oadt at level 0,
                                                e custom oadt at level 0).
Notation "'inl' < t > e" := (EInj true t e) (in custom oadt at level 0,
                                                t custom oadt at level 0,
                                                e custom oadt at level 0).
Notation "'inr' < t > e" := (EInj false t e) (in custom oadt at level 0,
                                                 t custom oadt at level 0,
                                                 e custom oadt at level 0).
Notation "'~inj@' b < t > e" := (EOInj b t e) (in custom oadt at level 0,
                                                  b custom oadt at level 0,
                                                  t custom oadt at level 0,
                                                  e custom oadt at level 0).
Notation "'~inl' < t > e" := (EOInj true t e) (in custom oadt at level 0,
                                                  t custom oadt at level 0,
                                                  e custom oadt at level 0).
Notation "'~inr' < t > e" := (EOInj false t e) (in custom oadt at level 0,
                                                   t custom oadt at level 0,
                                                   e custom oadt at level 0).
Notation "'case' e0 'of' x '=>' e1 '|' y '=>' e2" :=
  (ECase e0 x e1 y e2) (in custom oadt at level 89,
                           e0 custom oadt at level 99,
                           x custom oadt at level 99,
                           e1 custom oadt at level 99,
                           y custom oadt at level 99,
                           e2 custom oadt at level 99,
                           left associativity).
Notation "'~case' e0 'of' x '=>' e1 '|' y '=>' e2" :=
  (EOCase e0 x e1 y e2) (in custom oadt at level 89,
                            e0 custom oadt at level 99,
                            x custom oadt at level 99,
                            e1 custom oadt at level 99,
                            y custom oadt at level 99,
                            e2 custom oadt at level 99,
                            left associativity).
Notation "\ x : t '=>' e" := (EAbs x t e) (in custom oadt at level 90,
                                              x custom oadt at level 99,
                                              t custom oadt at level 99,
                                              e custom oadt at level 99,
                                              left associativity).
Notation "'fold' < X > e" := (EFold X e) (in custom oadt at level 0,
                                             X custom oadt at level 0,
                                             e custom oadt at level 0).
Notation "'unfold' < X > e" := (EUnfold X e) (in custom oadt at level 0,
                                                 X custom oadt at level 0,
                                                 e custom oadt at level 0).
Notation "[ ~ b ]" := (EBoxedLit b) (in custom oadt at level 0,
                                      b custom oadt at level 0).
Notation "[ '~inj@' b < t > e ]" := (EBoxedOInj b t e)
                                      (in custom oadt at level 0,
                                          b custom oadt at level 0,
                                          t custom oadt at level 0,
                                          e custom oadt at level 0).
Notation "[ '~inl' < t > e ]" := (EBoxedOInj true t e)
                                   (in custom oadt at level 0,
                                       t custom oadt at level 0,
                                       e custom oadt at level 0).
Notation "[ '~inr' < t > e ]" := (EBoxedOInj false t e)
                                   (in custom oadt at level 0,
                                       t custom oadt at level 0,
                                       e custom oadt at level 0).
Notation "'data' X := e" := (DADT X e) (in custom oadt at level 0,
                                           X custom oadt at level 0,
                                           e custom oadt at level 0).
Notation "'obliv' X [ x : t ] := e" := (DOADT X x t e)
                                         (in custom oadt at level 0,
                                             X custom oadt at level 0,
                                             x custom oadt at level 0,
                                             t custom oadt at level 0,
                                             e custom oadt at level 0).
Notation "'def' x : t := e" := (DFun x t e) (in custom oadt at level 0,
                                                x custom oadt at level 0,
                                                t custom oadt at level 0,
                                                e custom oadt at level 0).

(** * Dynamic semantics *)

(** ** Polynomial algebraic data type (α) *)
Inductive padt : expr -> Prop :=
| PUnitT : padt <{ 𝟙 }>
| PBool : padt <{ 𝔹 }>
| PProd α1 α2 : padt α1 -> padt α2 -> padt <{ α1 * α2 }>
| PSum α1 α2 : padt α1 -> padt α2 -> padt <{ α1 + α2 }>
| PName (X : name) : padt X
.

(** ** OADT values (ω) *)
Inductive tval : expr -> Prop :=
| VUnitT : tval <{ 𝟙 }>
| VOBool : tval <{ ~𝔹 }>
| VProd ω1 ω2 : tval ω1 -> tval ω2 -> tval <{ ω1 * ω2 }>
| VOSum ω1 ω2 : tval ω1 -> tval ω2 -> tval <{ ω1 ~+ ω2 }>
.

(** ** Values (v) *)
Inductive val : expr -> Prop :=
| VUnitV : val <{ () }>
| VLit (b : bool) : val <{ b }>
| VBoxedLit (b : bool) : val <{ [~b] }>
| VPair v1 v2 : val v1 -> val v2 -> val <{ (v1, v2) }>
| VAbs x τ e : val <{ \x:τ => e }>
| VInj b τ v : val v -> val <{ inj@b<τ> v }>
| VFold X v : val v -> val <{ fold<X> v }>
| VBoxedOInj b ω v : tval ω -> val v -> val <{ [~inj@b<ω> v] }>
.

(** ** Evaluation context (ℇ) *)
(* This style is inspired by Iron Lambda. *)
(** We define evaluation context [ℇ] as the hole-filling function. [ℇ e] fills
the hole in [ℇ] with [e]. [ectx ℇ] asserts that [ℇ] is a well-formed
context. *)
Inductive ectx : (expr -> expr) -> Prop :=
(* | CtxTop : ectx (fun e => e) *)
| CtxProd1 τ2 : ectx (fun τ1 => <{ τ1 * τ2 }>)
| CtxProd2 ω1 : tval ω1 -> ectx (fun τ2 => <{ ω1 * τ2 }>)
| CtxOSum1 τ2 : ectx (fun τ1 => <{ τ1 ~+ τ2 }>)
| CtxOSum2 ω1 : tval ω1 -> ectx (fun τ2 => <{ ω1 ~+ τ2 }>)
| CtxApp1 e2 : ectx (fun e1 => <{ e1 e2 }>)
| CtxApp2 v1 : val v1 -> ectx (fun e2 => <{ v1 e2 }>)
| CtxApp3 (x1 : name) : ectx (fun e2 => <{ x1 e2 }>)
| CtxSec : ectx (fun e => <{ s𝔹 e }>)
| CtxRet : ectx (fun e => <{ r𝔹 e }>)
| CtxIte e1 e2 : ectx (fun e0 => <{ if e0 then e1 else e2 }>)
| CtxMux1 e1 e2 : ectx (fun e0 => <{ mux e0 e1 e2 }>)
| CtxMux2 v0 e2 : val v0 -> ectx (fun e1 => <{ mux v0 e1 e2 }>)
| CtxMux3 v0 v1 : val v0 -> val v1 -> ectx (fun e2 => <{ mux v0 v1 e2 }>)
| CtxPair1 e2 : ectx (fun e1 => <{ (e1, e2) }>)
| CtxPair2 v1 : val v1 -> ectx (fun e2 => <{ (v1, e2) }>)
| CtxLetP x1 x2 e2 : ectx (fun e1 => <{ let (x1, x2) = e1 in e2 }>)
| CtxInj b τ : ectx (fun e => <{ inj@b<τ> e }>)
| CtxCase x1 e1 x2 e2: ectx (fun e0 => <{ case e0 of x1 => e1 | x2 => e2 }>)
| CtxOInj1 b e : ectx (fun τ => <{ ~inj@b<τ> e }>)
| CtxOInj2 b ω : tval ω -> ectx (fun e => <{ ~inj@b<ω> e }>)
| CtxOCase x1 e1 x2 e2: ectx (fun e0 => <{ ~case e0 of x1 => e1 | x2 => e2 }>)
| CtxLet x e2 : ectx (fun e1 => <{ let x = e1 in e2 }>)
| CtxFold X : ectx (fun e => <{ fold<X> e }>)
| CtxUnfold X : ectx (fun e => <{ unfold<X> e }>)
.

(** ** Substitution *)
Reserved Notation "'[' s '/' x ']' e" (in custom oadt at level 0, x constr).
Fixpoint subst (x : name) (s : expr) (e : expr) : expr :=
  match e with
  | <{ τ1 * τ2 }> => <{ [s/x]τ1 * [s/x]τ2 }>
  | <{ τ1 + τ2 }> => <{ [s/x]τ1 + [s/x]τ2 }>
  | <{ τ1 ~+ τ2 }> => <{ [s/x]τ1 ~+ [s/x]τ2 }>
  (* TODO *)
  | <{ Π y : τ1, τ2 }> => if decide (x = y) then e else <{ Π y : τ1, [s/x]τ2 }>
  | <{ !y }> => if decide (x = y) then s else e
  | <{ e1 e2 }> => <{ ([s/x]e1) ([s/x]e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ([s/x]e) }>
  | <{ r𝔹 e }> => <{ r𝔹 ([s/x]e) }>
  | <{ if e0 then e1 else e2 }> => <{ if [s/x]e0 then [s/x]e1 else [s/x]e2 }>
  | <{ mux e0 e1 e2 }> => <{ mux ([s/x]e0) ([s/x]e1) ([s/x]e2) }>
  | <{ (e1, e2) }> => <{ ([s/x]e1, [s/x]e2) }>
  | <{ let (y1, y2) = e1 in e2 }> => s
  | <{ inj@b<τ> e }> => <{ inj@b<τ> ([s/x]e) }>
  | <{ case e0 of y1 => e1 | y2 => e2 }> => s
  | <{ ~inj@b<τ> e }> => s
  | <{ ~case e0 of y1 => e1 | y2 => e2 }> => s
  (* TODO: τ? *)
  | <{ \y:τ => e' }> => if decide (x = y) then e else <{ \y:τ => [s/x]e' }>
  | <{ let y = e1 in e2 }> => s
  | <{ fold<X> e }> => <{ fold<X> ([s/x]e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ([s/x]e) }>
  | _ => e
  end
where "'[' s '/' x ']' e" := (subst x s e) (in custom oadt).

End lang.

End oadt.
