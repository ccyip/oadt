From oadt.lang_oadt Require Import base.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Open Scope type_scope.

(** * Definitions *)

(** ** Obliviousness label *)
(** Defined as alias of [bool]. An oblivious construct (with [LObliv] label) may
accept oblivious components, and a public construct (with [LPub] label) only
accepts public components. *)
Notation olabel := bool (only parsing).
Notation LObliv := true (only parsing).
Notation LPub := false (only parsing).

(** ** Expressions (e, τ) *)
(** We use locally nameless representation for binders. *)
Inductive expr :=
(* Locally bound variables, i.e. de Bruijn indices. *)
| EBVar (k : nat)
(* Free variables *)
| EFVar (x : atom)
(* Global variables, referring to global functions, ADTs and OADTs. *)
| EGVar (x : atom)
(* Functions *)
| EPi (τ1 τ2: expr)
| EAbs (τ e : expr)
| EApp (e1 e2 : expr)
(* Oblivious type application *)
| ETApp (X : atom) (e : expr)
(* Let binding *)
| ELet (e1 e2 : expr)
(* Unit *)
| EUnitT
| EUnitV
(* Public and oblivious Booleans *)
| EBool (l : olabel)
| ELit (b : bool)
(* Boolean section *)
| ESec (e : expr)
(* Public conditional. *)
| EIte (e0 e1 e2 : expr)
(* Public and oblivious product, pair and projection. Technically we do not need
to distinguish bewteen public and oblivious product, but this is conceptually
cleaner in my opinion. It also makes certain aspects of semantics and type
checking more convenient. Note that the oblivious label can be easily inferred
and elaborated, so the surface language needs not distinguish them. *)
| EProd (l : olabel) (τ1 τ2 : expr)
| EPair (l : olabel) (e1 e2 : expr)
| EProj (l : olabel) (b : bool) (e : expr)
(* Public and oblivious sum, injection and case analysis. *)
| ESum (l : olabel) (τ1 τ2 : expr)
| EInj (l : olabel) (b : bool) (τ e : expr)
| ECase (l : olabel) (e0 : expr) (e1 : expr) (e2 : expr)
(* Introduction and elimination of ADTs *)
| EFold (X : atom) (e : expr)
| EUnfold (X : atom) (e : expr)
(* Oblivious conditional, i.e. MUX. *)
| EMux (e0 e1 e2 : expr)
(* Runtime expressions *)
| EBoxedLit (b : bool)
| EBoxedInj (b : bool) (τ e : expr)
.

(** [expr] has decidable equality. *)
#[global]
Instance expr_eq : EqDecision expr.
Proof.
  solve_decision.
Defined.

(** ** Global definitions (D) *)
Variant gdef :=
| DADT (e : expr)
| DOADT (τ e : expr)
| DFun (t : expr) (e : expr)
.

(** ** Global context (Σ) *)
(** A store of global definitions. *)
Definition gctx := amap gdef.

(** This type class trick allows us to omit the global context parameter when it
is available as section variables. *)
Existing Class gctx.
#[export]
Hint Extern 1 (gctx) => assumption : typeclass_instances.
#[export]
Hint Unfold gctx : typeclass_instances.

(** ** Programs (P) *)
Notation program := (gctx * expr).


(** * Notations for expressions *)
Module expr_notations.

(* Adapted from _Software Foundations_. *)
Coercion ELit : bool >-> expr.

(** Quote *)
Notation "<{ e }>" := e (e custom oadt at level 99).
(** Lispy unquote *)
Notation "',(' e ')'" := e (in custom oadt at level 0,
                               e constr at level 0).

Notation "( x )" := x (in custom oadt, x at level 99).
Notation "x" := x (in custom oadt at level 0, x constr at level 0).
Notation "'bvar' x" := (EBVar x) (in custom oadt at level 0, x constr at level 0).
Notation "'fvar' x" := (EFVar x) (in custom oadt at level 0, x constr at level 0,
                             only parsing).
Notation "'gvar' x" := (EGVar x) (in custom oadt at level 0, x constr at level 0).
Notation "'lit' b" := (ELit b) (in custom oadt at level 0, b constr at level 0,
                            only parsing).
Notation "'𝟙'" := EUnitT (in custom oadt at level 0).
Notation "'Unit'" := EUnitT (in custom oadt at level 0, only parsing).
Notation "'𝔹{' l '}'" := (EBool l) (in custom oadt at level 0,
                               l constr at level 0,
                               format "'𝔹{' l '}'").
Notation "'𝔹'" := (EBool LPub) (in custom oadt at level 0).
Notation "'Bool'" := (EBool LPub) (in custom oadt at level 0, only parsing).
Notation "'~𝔹'" := (EBool LObliv) (in custom oadt at level 0).
Notation "'~Bool'" := (EBool LObliv) (in custom oadt at level 0, only parsing).
Notation "τ1 '*{' l '}' τ2" := (EProd l τ1 τ2) (in custom oadt at level 3,
                                     l constr at level 0,
                                     τ1 custom oadt,
                                     τ2 custom oadt at level 0,
                                     format "τ1  '*{' l '}'  τ2").
Notation "τ1 * τ2" := (EProd LPub τ1 τ2) (in custom oadt at level 3,
                            τ1 custom oadt,
                            τ2 custom oadt at level 0).
Notation "τ1 ~* τ2" := (EProd LObliv τ1 τ2) (in custom oadt at level 3,
                             τ1 custom oadt,
                             τ2 custom oadt at level 0).
Notation "τ1 '+{' l '}' τ2" := (ESum l τ1 τ2) (in custom oadt at level 4,
                                     l constr at level 0,
                                     left associativity,
                                     format "τ1  '+{' l '}'  τ2").
Notation "τ1 + τ2" := (ESum LPub τ1 τ2) (in custom oadt at level 4,
                            left associativity).
Notation "τ1 ~+ τ2" := (ESum LObliv τ1 τ2) (in custom oadt at level 4,
                             left associativity).
Notation "'Π' : τ1 , τ2" := (EPi τ1 τ2)
                              (in custom oadt at level 50,
                                  right associativity,
                                  format "Π : τ1 ,  τ2").
Notation "\ : τ '=>' e" := (EAbs τ e)
                             (in custom oadt at level 90,
                                 τ custom oadt at level 99,
                                 e custom oadt at level 99,
                                 left associativity,
                                 format "\ : τ  =>  e").
Notation "e1 e2" := (EApp e1 e2) (in custom oadt at level 2, left associativity).
Notation "X @ e" := (ETApp X e) (in custom oadt at level 2,
                          format "X @ e").
Notation "()" := EUnitV (in custom oadt at level 0).
Notation "( x , y , .. , z ){ l }" := (EPair l .. (EPair l x y) .. z)
                                        (in custom oadt at level 0,
                                            l constr at level 0,
                                            x custom oadt at level 99,
                                            y custom oadt at level 99,
                                            z custom oadt at level 99,
                                            format "( x ,  y ,  .. ,  z ){ l }").
Notation "( x , y , .. , z )" := (EPair LPub .. (EPair LPub x y) .. z)
                                   (in custom oadt at level 0,
                                       x custom oadt at level 99,
                                       y custom oadt at level 99,
                                       z custom oadt at level 99).
Notation "~( x , y , .. , z )" := (EPair LObliv .. (EPair LObliv x y) .. z)
                                    (in custom oadt at level 0,
                                        x custom oadt at level 99,
                                        y custom oadt at level 99,
                                        z custom oadt at level 99,
                                        format "~( x ,  y ,  .. ,  z )").
Notation "'π{' l '}@' b e" := (EProj l b e) (in custom oadt at level 2,
                                    l constr at level 0,
                                    b constr at level 0,
                                    format "π{ l }@ b  e").
Notation "'π@' b e" := (EProj LPub b e) (in custom oadt at level 2,
                             b constr at level 0,
                             format "π@ b  e").
Notation "'~π@' b e" := (EProj LObliv b e) (in custom oadt at level 2,
                              b constr at level 0,
                              format "~π@ b  e").
Notation "'π1' e" := (EProj LPub true e) (in custom oadt at level 2).
Notation "'π2' e" := (EProj LPub false e) (in custom oadt at level 2).
Notation "'~π1' e" := (EProj LObliv true e) (in custom oadt at level 2).
Notation "'~π2' e" := (EProj LObliv false e) (in custom oadt at level 2).
Notation "'s𝔹' e" := (ESec e) (in custom oadt at level 2).
Notation "'if' e0 'then' e1 'else' e2" := (EIte e0 e1 e2)
                                            (in custom oadt at level 89,
                                                e0 custom oadt at level 99,
                                                e1 custom oadt at level 99,
                                                e2 custom oadt at level 99,
                                                left associativity).
Notation "'let' e1 'in' e2" := (ELet e1 e2)
                                 (in custom oadt at level 0,
                                     e1 custom oadt at level 99,
                                     e2 custom oadt at level 99).
Notation "'inj{' l '}@' b < τ > e" := (EInj l b τ e) (in custom oadt at level 2,
                                            l constr at level 0,
                                            b constr at level 0,
                                            τ custom oadt at level 0,
                                            format "'inj{' l '}@' b < τ >  e").
Notation "'inl{' l '}' < τ > e" := (EInj l true τ e) (in custom oadt at level 2,
                                         τ custom oadt at level 0,
                                         format "inl{ l } < τ >  e").
Notation "'inr{' l '}' < τ > e" := (EInj l false τ e) (in custom oadt at level 2,
                                         τ custom oadt at level 0,
                                         format "inr{ l } < τ >  e").
Notation "'inj@' b < τ > e" := (EInj LPub b τ e) (in custom oadt at level 2,
                                     b constr at level 0,
                                     τ custom oadt at level 0,
                                     format "inj@ b < τ >  e").
Notation "'inl' < τ > e" := (EInj LPub true τ e) (in custom oadt at level 2,
                                  τ custom oadt at level 0,
                                  format "inl < τ >  e").
Notation "'inr' < τ > e" := (EInj LPub false τ e) (in custom oadt at level 2,
                                  τ custom oadt at level 0,
                                  format "inr < τ >  e").
Notation "'~inj@' b < τ > e" := (EInj LObliv b τ e) (in custom oadt at level 2,
                                      b constr at level 0,
                                      τ custom oadt at level 0,
                                      format "~inj@ b < τ >  e").
Notation "'~inl' < τ > e" := (EInj LObliv true τ e) (in custom oadt at level 2,
                                   τ custom oadt at level 0,
                                   format "~inl < τ >  e").
Notation "'~inr' < τ > e" := (EInj LObliv false τ e) (in custom oadt at level 2,
                                   τ custom oadt at level 0,
                                   format "~inr < τ >  e").
Notation "'case{' l '}' e0 'of' e1 '|' e2" :=
  (ECase l e0 e1 e2) (in custom oadt at level 89,
        l constr at level 0,
        e0 custom oadt at level 99,
        e1 custom oadt at level 99,
        e2 custom oadt at level 99,
        left associativity,
        format "'case{' l '}'  e0  'of'  e1  '|'  e2").
Notation "'case' e0 'of' e1 '|' e2" :=
  (ECase LPub e0 e1 e2) (in custom oadt at level 89,
        e0 custom oadt at level 99,
        e1 custom oadt at level 99,
        e2 custom oadt at level 99,
        left associativity).
Notation "'~case' e0 'of' e1 '|' e2" :=
  (ECase LObliv e0 e1 e2) (in custom oadt at level 89,
        e0 custom oadt at level 99,
        e1 custom oadt at level 99,
        e2 custom oadt at level 99,
        left associativity).
Notation "'fold' < X > e" := (EFold X e) (in custom oadt at level 2,
                                   X custom oadt at level 0,
                                   format "fold < X >  e").
Notation "'unfold' < X > e" := (EUnfold X e) (in custom oadt at level 2,
                                     X custom oadt at level 0,
                                     format "unfold < X >  e").
Notation "'mux' e0 e1 e2" := (EMux e0 e1 e2) (in custom oadt at level 2,
                                   e0 custom oadt at level 0,
                                   e1 custom oadt at level 0,
                                   e2 custom oadt at level 0).

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

Notation "'ite' e0 e1 e2" := (if e0 then e1 else e2)
                               (in custom oadt at level 2,
                                   e0 constr at level 0,
                                   e1 custom oadt at level 0,
                                   e2 custom oadt at level 0).

End expr_notations.


(** * More Definitions *)
Section definitions.

Import expr_notations.
#[local]
Coercion EFVar : atom >-> expr.

(** ** Variable opening  *)
Reserved Notation "'{' k '~>' s '}' e" (in custom oadt at level 20, k constr).

Fixpoint open_ (k : nat) (s : expr) (e : expr) : expr :=
  match e with
  | <{ bvar n }> => if decide (k = n) then s else e
  | <{ Π:τ1, τ2 }> => <{ Π:({k~>s}τ1), {S k~>s}τ2 }>
  | <{ \:τ => e }> => <{ \:({k~>s}τ) => {S k~>s}e }>
  | <{ let e1 in e2 }> => <{ let {k~>s}e1 in {S k~>s}e2 }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {k~>s}e0 of {S k~>s}e1 | {S k~>s}e2 }>
  (* Congruence rules *)
  | <{ e1 e2 }> => <{ ({k~>s}e1) ({k~>s}e2) }>
  | <{ X@e }> => <{ X@({k~>s}e) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({k~>s}e) }>
  | <{ if e0 then e1 else e2 }> => <{ if {k~>s}e0 then {k~>s}e1 else {k~>s}e2 }>
  | <{ τ1 *{l} τ2 }> => <{ ({k~>s}τ1) *{l} ({k~>s}τ2) }>
  | <{ (e1, e2){l} }> => <{ ({k~>s}e1, {k~>s}e2){l} }>
  | <{ π{l}@b e }> => <{ π{l}@b ({k~>s}e) }>
  | <{ τ1 +{l} τ2 }> => <{ ({k~>s}τ1) +{l} ({k~>s}τ2) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({k~>s}τ)> ({k~>s}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({k~>s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({k~>s}e) }>
  | <{ mux e0 e1 e2 }> => <{ mux ({k~>s}e0) ({k~>s}e1) ({k~>s}e2) }>
  | _ => e
  end

where "'{' k '~>' s '}' e" := (open_ k s e) (in custom oadt).

Definition open s e := open_ 0 s e.
Notation "e ^ s" := (open s e) (in custom oadt at level 20).

(** ** Substitution *)
Reserved Notation "'{' x '↦' s '}' e" (in custom oadt at level 20, x constr).

Fixpoint subst (x : atom) (s : expr) (e : expr) : expr :=
  match e with
  | <{ fvar y }> => if decide (x = y) then s else e
  (* Congruence rules *)
  | <{ Π:τ1, τ2 }> => <{ Π:({x↦s}τ1), {x↦s}τ2 }>
  | <{ \:τ => e }> => <{ \:({x↦s}τ) => {x↦s}e }>
  | <{ e1 e2 }> => <{ ({x↦s}e1) ({x↦s}e2) }>
  | <{ X@e }> => <{ X@({x↦s}e) }>
  | <{ let e1 in e2 }> => <{ let {x↦s}e1 in {x↦s}e2 }>
  | <{ s𝔹 e }> => <{ s𝔹 ({x↦s}e) }>
  | <{ if e0 then e1 else e2 }> => <{ if {x↦s}e0 then {x↦s}e1 else {x↦s}e2 }>
  | <{ τ1 *{l} τ2 }> => <{ ({x↦s}τ1) *{l} ({x↦s}τ2) }>
  | <{ (e1, e2){l} }> => <{ ({x↦s}e1, {x↦s}e2){l} }>
  | <{ π{l}@b e }> => <{ π{l}@b ({x↦s}e) }>
  | <{ τ1 +{l} τ2 }> => <{ ({x↦s}τ1) +{l} ({x↦s}τ2) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({x↦s}τ)> ({x↦s}e) }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {x↦s}e0 of {x↦s}e1 | {x↦s}e2 }>
  | <{ fold<X> e }> => <{ fold<X> ({x↦s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({x↦s}e) }>
  | <{ mux e0 e1 e2 }> => <{ mux ({x↦s}e0) ({x↦s}e1) ({x↦s}e2) }>
  | _ => e
  end

where "'{' x '↦' s '}' e" := (subst x s e) (in custom oadt).

(** ** Oblivious type values (ω) *)
Inductive otval : expr -> Prop :=
| OVUnitT : otval <{ 𝟙 }>
| OVOBool : otval <{ ~𝔹 }>
| OVProd ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 ~* ω2 }>
| OVOSum ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 ~+ ω2 }>
.

(** ** Oblivious values (v) *)
Inductive oval : expr -> Prop :=
| OVUnitV : oval <{ () }>
| OVBoxedLit b : oval <{ [b] }>
| OVPair v1 v2 : oval v1 -> oval v2 -> oval <{ ~(v1, v2) }>
| OVBoxedInj b ω v : otval ω -> oval v -> oval <{ [inj@b<ω> v] }>
.

(** ** Values (v) *)
Inductive val : expr -> Prop :=
| VLit b : val <{ lit b }>
| VPair v1 v2 : val v1 -> val v2 -> val <{ (v1, v2) }>
| VAbs τ e : val <{ \:τ => e }>
| VInj b τ v : val v -> val <{ inj@b<τ> v }>
| VFold X v : val v -> val <{ fold<X> v }>
| VOVal v : oval v -> val v
.

(** ** Local closure and well-formedness of expressions *)
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
| LCCase l e0 e1 e2 L1 L2 :
  (forall x, x ∉ L1 -> lc <{ e1^x }>) ->
  (forall x, x ∉ L2 -> lc <{ e2^x }>) ->
  lc e0 -> lc <{ case{l} e0 of e1 | e2 }>
(* Congruence rules *)
| LCUnitT : lc <{ 𝟙 }>
| LCUnitV : lc <{ () }>
| LCBool l : lc <{ 𝔹{l} }>
| LCApp e1 e2 : lc e1 -> lc e2 -> lc <{ e1 e2 }>
| LCTApp X e : lc e -> lc <{ X@e }>
| LCLit b : lc <{ lit b }>
| LCSec e : lc e -> lc <{ s𝔹 e }>
| LCIte e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ if e0 then e1 else e2 }>
| LCProd l τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 *{l} τ2 }>
| LCPair l e1 e2 : lc e1 -> lc e2 -> lc <{ (e1, e2){l} }>
| LCProj l b e : lc e -> lc <{ π{l}@b e }>
| LCSum l τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 +{l} τ2 }>
| LCInj l b τ e : lc τ -> lc e -> lc <{ inj{l}@b<τ> e }>
| LCFold X e : lc e -> lc <{ fold<X> e }>
| LCUnfold X e : lc e -> lc <{ unfold<X> e }>
| LCMux e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ mux e0 e1 e2 }>
| LCBoxedLit b : lc <{ [b] }>
(* Techincally this is not only locally closed, but more about
well-formedness. *)
| LCBoxedInj b ω v : otval ω -> oval v -> lc <{ [inj@b<ω> v] }>
.

End definitions.

(** * Notations *)
Module notations.

Export expr_notations.

Notation "'{' k '~>' s '}' e" := (open_ k s e)
                                   (in custom oadt at level 20, k constr).
Notation "e ^ s" := (open s e) (in custom oadt at level 20).

Notation "'{' x '↦' s '}' e" := (subst x s e)
                                  (in custom oadt at level 20, x constr).

(* This notation is supposed to be applied to a typing context. *)
Notation "{ x '↦' s }" := (subst x s) (at level 20).

Notation "x # s" := (x ∉ stale s) (at level 40).

End notations.
