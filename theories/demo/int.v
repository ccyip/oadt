(** This file extends the core calculus with bounded primitive integers. We do
not prove the metatheories for this extension. *)
From Coq Require Import Int63.Int63.
From oadt Require Import prelude.
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.typing.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Import Int63.

(** We reuse the same names as in the core calculus. Many definitions and lemmas
are redefined against the extensions. *)

(** * Syntax *)

(** ** Expressions (e, τ) *)
Inductive expr :=
| EBVar (k : nat)
| EFVar (x : atom)
| EGVar (x : atom)
| EPi (l : llabel) (τ1 τ2: expr)
| EAbs (l : llabel) (τ e : expr)
| EApp (e1 e2 : expr)
| ELet (e1 e2 : expr)
| EUnitT
| EUnitV
| EBool (l : olabel)
| ELit (b : bool)
| ESec (e : expr)
| EIte (l : olabel) (e0 e1 e2 : expr)
| EProd (τ1 τ2 : expr)
| EPair (e1 e2 : expr)
| EProj (b : bool) (e : expr)
| ESum (l : olabel) (τ1 τ2 : expr)
| EInj (l : olabel) (b : bool) (τ e : expr)
| ECase (l : olabel) (e0 : expr) (e1 : expr) (e2 : expr)
| EFold (X : atom) (e : expr)
| EUnfold (X : atom) (e : expr)
| ETape (e : expr)
| EMux (e0 e1 e2 : expr)
| EBoxedLit (b : bool)
| EBoxedInj (b : bool) (τ e : expr)
(* NOTE: Extensions *)
| EInt (l : olabel)
| EIntLit (i : int)
| EIntLe (l : olabel) (e1 e2 : expr)
| EIntSec (e :expr)
| EIntRet (e :expr)
| EBoxedIntLit (i : int)
.

(** ** Expressions with leakage label (T) *)
Definition lexpr := (llabel * expr).
Definition lexpr_label : lexpr -> llabel := fst.
Arguments lexpr_label /.
Definition lexpr_expr : lexpr -> expr := snd.
Arguments lexpr_expr /.

(** ** Global definitions (D) *)
Variant gdef :=
| DADT (e : expr)
| DOADT (τ e : expr)
| DFun (T : lexpr) (e : expr)
.

(** ** Global context (Σ) *)
Notation gctx := (amap gdef).

(** ** Programs (P) *)
Notation program := (gctx * expr).

(** ** Notations *)
Module int_notations.

Coercion ELit : bool >-> expr.
Coercion lexpr_expr : lexpr >-> expr.

Notation "<{ e }>" := e (e custom oadt at level 99).
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
Notation "τ1 * τ2" := (EProd τ1 τ2) (in custom oadt at level 3,
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
Notation "'Π' :{ l } τ1 , τ2" := (EPi l τ1 τ2)
                                   (in custom oadt at level 50,
                                       right associativity,
                                       format "Π :{ l } τ1 ,  τ2").
Notation "'Π' : τ1 , τ2" := (EPi LSafe τ1 τ2)
                              (in custom oadt at level 50,
                                  right associativity,
                                  format "Π : τ1 ,  τ2").
Notation "'Π' ~: τ1 , τ2" := (EPi LLeak τ1 τ2)
                               (in custom oadt at level 50,
                                   right associativity,
                                   format "Π ~: τ1 ,  τ2").
Notation "\ :{ l } τ '=>' e" := (EAbs l τ e)
                                  (in custom oadt at level 90,
                                      τ custom oadt at level 99,
                                      e custom oadt at level 99,
                                      left associativity,
                                      format "\ :{ l } τ  =>  e").
Notation "\ : τ '=>' e" := (EAbs LSafe τ e)
                             (in custom oadt at level 90,
                                 τ custom oadt at level 99,
                                 e custom oadt at level 99,
                                 left associativity,
                                 format "\ : τ  =>  e").
Notation "\ ~: τ '=>' e" := (EAbs LLeak τ e)
                              (in custom oadt at level 90,
                                  τ custom oadt at level 99,
                                  e custom oadt at level 99,
                                  left associativity,
                                  format "\ ~: τ  =>  e").
Notation "e1 e2" := (EApp e1 e2) (in custom oadt at level 2, left associativity).
Notation "()" := EUnitV (in custom oadt at level 0).
Notation "( x , y , .. , z )" := (EPair .. (EPair x y) .. z)
                                   (in custom oadt at level 0,
                                       x custom oadt at level 99,
                                       y custom oadt at level 99,
                                       z custom oadt at level 99).
Notation "'π@' b e" := (EProj b e) (in custom oadt at level 2,
                                       b constr at level 0,
                                       format "π@ b  e").
Notation "'π1' e" := (EProj true e) (in custom oadt at level 2).
Notation "'π2' e" := (EProj false e) (in custom oadt at level 2).
Notation "'s𝔹' e" := (ESec e) (in custom oadt at level 2).
Notation "'if{' l '}' e0 'then' e1 'else' e2" := (EIte l e0 e1 e2)
                                                   (in custom oadt at level 89,
                                                       l constr at level 0,
                                                       e0 custom oadt at level 99,
                                                       e1 custom oadt at level 99,
                                                       e2 custom oadt at level 99,
                                                       left associativity,
                                                       format "'if{' l '}'  e0  'then'  e1  'else'  e2").
Notation "'if' e0 'then' e1 'else' e2" := (EIte LPub e0 e1 e2)
                                            (in custom oadt at level 89,
                                                e0 custom oadt at level 99,
                                                e1 custom oadt at level 99,
                                                e2 custom oadt at level 99,
                                                left associativity).
Notation "'~if' e0 'then' e1 'else' e2" := (EIte LObliv e0 e1 e2)
                                             (in custom oadt at level 89,
                                                 e0 custom oadt at level 99,
                                                 e1 custom oadt at level 99,
                                                 e2 custom oadt at level 99).
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
Notation "'tape' e" := (ETape e) (in custom oadt at level 2).
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

Notation "'r𝔹' e" := <{ ~if e then true else false }> (in custom oadt at level 2).

(* NOTE: Extensions *)
Notation "'int{' l '}'" := (EInt l) (in custom oadt,
                                        l constr at level 0,
                                        format "'int{' l '}'").
Notation "'int'" := (EInt LPub) (in custom oadt).
Notation "'~int'" := (EInt LObliv) (in custom oadt).
Notation "a '<={' l '}' b" := (EIntLe l a b) (in custom oadt at level 3,
                                                 l constr,
                                                 a custom oadt,
                                                 b custom oadt,
                                                 no associativity,
                                                 format "a  '<={' l '}'  b").
Notation "a '<=' b" := (EIntLe LPub a b) (in custom oadt at level 3,
                                             a custom oadt,
                                             b custom oadt,
                                             no associativity).
Notation "a '~<=' b" := (EIntLe LObliv a b) (in custom oadt at level 3,
                                                a custom oadt,
                                                b custom oadt,
                                                no associativity).
Notation "'s_int' e" := (EIntSec e) (in custom oadt at level 2).
Notation "'r_int' e" := (EIntRet e) (in custom oadt at level 2).
Notation "'i(' a ')'" := (EIntLit a) (in custom oadt at level 0,
                                         a constr at level 0,
                                         format "'i(' a ')'").
Notation "'i[' a ']'" := (EBoxedIntLit a) (in custom oadt at level 0,
                                              a constr at level 0,
                                              format "'i[' a ]").

End int_notations.

Import int_notations.
#[local]
Coercion EFVar : atom >-> expr.


(** ** Variable opening  *)
Section definitions.

Reserved Notation "'{' k '~>' s '}' e" (in custom oadt at level 20, k constr).

Fixpoint open_ (k : nat) (s : expr) (e : expr) : expr :=
  match e with
  | <{ bvar n }> => if decide (k = n) then s else e
  | <{ Π:{l}τ1, τ2 }> => <{ Π:{l}({k~>s}τ1), {S k~>s}τ2 }>
  | <{ \:{l}τ => e }> => <{ \:{l}({k~>s}τ) => {S k~>s}e }>
  | <{ let e1 in e2 }> => <{ let {k~>s}e1 in {S k~>s}e2 }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {k~>s}e0 of {S k~>s}e1 | {S k~>s}e2 }>
  (* Congruence rules *)
  | <{ e1 e2 }> => <{ ({k~>s}e1) ({k~>s}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({k~>s}e) }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} {k~>s}e0 then {k~>s}e1 else {k~>s}e2 }>
  | <{ τ1 * τ2 }> => <{ ({k~>s}τ1) * ({k~>s}τ2) }>
  | <{ (e1, e2) }> => <{ ({k~>s}e1, {k~>s}e2) }>
  | <{ π@b e }> => <{ π@b ({k~>s}e) }>
  | <{ τ1 +{l} τ2 }> => <{ ({k~>s}τ1) +{l} ({k~>s}τ2) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({k~>s}τ)> ({k~>s}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({k~>s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({k~>s}e) }>
  | <{ tape e }> => <{ tape ({k~>s}e) }>
  | <{ mux e0 e1 e2 }> => <{ mux ({k~>s}e0) ({k~>s}e1) ({k~>s}e2) }>
  (* NOTE: Extensions *)
  | <{ e1 <={l} e2 }> => <{ ({k~>s}e1) <={l} ({k~>s}e2) }>
  | <{ s_int e }> => <{ s_int ({k~>s}e) }>
  | <{ r_int e }> => <{ r_int ({k~>s}e) }>
  | _ => e
  end

where "'{' k '~>' s '}' e" := (open_ k s e) (in custom oadt).

Definition open s e := open_ 0 s e.
Notation "e ^ s" := (open s e) (in custom oadt at level 20).

(** ** Oblivious type values (ω) *)
Inductive otval : expr -> Prop :=
| OVUnitT : otval <{ 𝟙 }>
| OVOBool : otval <{ ~𝔹 }>
| OVProd ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 * ω2 }>
| OVOSum ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 ~+ ω2 }>
(* NOTE: Extensions *)
| OVOInt : otval <{ ~int }>
.

(** ** Oblivious values (v) *)
Inductive oval : expr -> Prop :=
| OVUnitV : oval <{ () }>
| OVBoxedLit b : oval <{ [b] }>
| OVPair v1 v2 : oval v1 -> oval v2 -> oval <{ (v1, v2) }>
| OVBoxedInj b ω v : otval ω -> oval v -> oval <{ [inj@b<ω> v] }>
(* NOTE: Extensions *)
| OVOIntLit n : oval <{ i[n] }>
.

(** ** Values (v) *)
Inductive val : expr -> Prop :=
| VUnitV : val <{ () }>
| VLit b : val <{ lit b }>
| VPair v1 v2 : val v1 -> val v2 -> val <{ (v1, v2) }>
| VAbs l τ e : val <{ \:{l}τ => e }>
| VInj b τ v : val v -> val <{ inj@b<τ> v }>
| VFold X v : val v -> val <{ fold<X> v }>
| VBoxedLit b : val <{ [b] }>
| VBoxedInj b ω v : otval ω -> oval v -> val <{ [inj@b<ω> v] }>
(* NOTE: Extensions *)
| VIntLit n : val <{ i(n) }>
| VIntBoxedLit n : val <{ i[n] }>
.

(** ** Local closure and well-formedness of expressions *)
Inductive lc : expr -> Prop :=
| LCFVar x : lc <{ fvar x }>
| LCGVar x : lc <{ gvar x }>
| LCPi l τ1 τ2 L :
    (forall x, x ∉ L -> lc <{ τ2^x }>) ->
    lc τ1 -> lc <{ Π:{l}τ1, τ2 }>
| LCAbs l τ e L :
    (forall x, x ∉ L -> lc <{ e^x }>) ->
    lc τ -> lc <{ \:{l}τ => e }>
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
| LCLit b : lc <{ lit b }>
| LCSec e : lc e -> lc <{ s𝔹 e }>
| LCIte l e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ if{l} e0 then e1 else e2 }>
| LCProd τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 * τ2 }>
| LCPair e1 e2 : lc e1 -> lc e2 -> lc <{ (e1, e2) }>
| LCProj b e : lc e -> lc <{ π@b e }>
| LCSum l τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 +{l} τ2 }>
| LCInj l b τ e : lc τ -> lc e -> lc <{ inj{l}@b<τ> e }>
| LCFold X e : lc e -> lc <{ fold<X> e }>
| LCUnfold X e : lc e -> lc <{ unfold<X> e }>
| LCTape e : lc e -> lc <{ tape e }>
| LCMux e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ mux e0 e1 e2 }>
| LCBoxedLit b : lc <{ [b] }>
| LCBoxedInj b ω v : otval ω -> oval v -> lc <{ [inj@b<ω> v] }>
(* NOTE: Extensions *)
| LCInt l : lc <{ int{l} }>
| LCIntLit n : lc <{ i(n) }>
| LCIntLe l e1 e2 : lc e1 -> lc e2 -> lc <{ e1 <={l} e2 }>
| LCIntSec e : lc e -> lc <{ s_int e }>
| LCIntRet e : lc e -> lc <{ r_int e }>
| LCBoxedIntLit n : lc <{ i[n] }>
.

End definitions.

Module syntax_notations.

Export int_notations.

Notation "'{' k '~>' s '}' e" := (open_ k s e)
                                   (in custom oadt at level 20, k constr).
Notation "e ^ s" := (open s e) (in custom oadt at level 20).

Notation "x # s" := (x ∉ stale s) (at level 40).

End syntax_notations.

Import syntax_notations.

(** * Semantics *)

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
(* NOTE: Extensions *)
| WIntLit n : wval <{ i(n) }>
| WBoxedIntLit n : wval <{ i[n] }>
| WIntRet n : wval <{ r_int i[n] }>
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
(* NOTE: Extensions *)
| OWBoxedIntLit n : woval <{ i[n] }>
.


(** ** OADT value typing *)
Inductive ovalty : expr -> expr -> Prop :=
| OTUnitV : ovalty <{ () }> <{ 𝟙 }>
| OTOBool b : ovalty <{ [b] }> <{ ~𝔹 }>
| OTPair v1 v2 ω1 ω2 :
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    ovalty <{ (v1, v2) }> <{ ω1 * ω2 }>
| OTOSum b v ω1 ω2 :
    ovalty v <{ ite b ω1 ω2 }> ->
    otval <{ ite b ω2 ω1 }> ->
    ovalty <{ [inj@b<ω1 ~+ ω2> v] }> <{ ω1 ~+ ω2 }>
(* NOTE: Extensions *)
| OTOInt n : ovalty <{ i[n] }> <{ ~int }>
.

(** ** Evaluation context (ℇ) *)
Variant ectx : (expr -> expr) -> Prop :=
| CtxProd1 τ2 : ectx (fun τ1 => <{ τ1 * τ2 }>)
| CtxProd2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 * τ2 }>)
| CtxOSum1 τ2 : ectx (fun τ1 => <{ τ1 ~+ τ2 }>)
| CtxOSum2 ω1 : otval ω1 -> ectx (fun τ2 => <{ ω1 ~+ τ2 }>)
| CtxApp1 v2 : wval v2 -> ectx (fun e1 => <{ e1 v2 }>)
| CtxApp2 e1 : ectx (fun e2 => <{ e1 e2 }>)
| CtxLet e2 : ectx (fun e1 => <{ let e1 in e2 }>)
| CtxSec : ectx (fun e => <{ s𝔹 e }>)
| CtxIte e1 e2 : ectx (fun e0 => <{ if e0 then e1 else e2 }>)
| CtxOIte1 e1 e2 : ectx (fun e0 => <{ ~if e0 then e1 else e2 }>)
| CtxOIte2 v0 e2 : wval v0 -> ectx (fun e1 => <{ ~if v0 then e1 else e2 }>)
| CtxOIte3 v0 v1 : wval v0 -> wval v1 -> ectx (fun e2 => <{ ~if v0 then v1 else e2 }>)
| CtxPair1 e2 : ectx (fun e1 => <{ (e1, e2) }>)
| CtxPair2 v1 : wval v1 -> ectx (fun e2 => <{ (v1, e2) }>)
| CtxProj b : ectx (fun e => <{ π@b e }>)
| CtxInj b τ : ectx (fun e => <{ inj@b<τ> e }>)
| CtxOInj1 b e : ectx (fun τ => <{ ~inj@b<τ> e }>)
| CtxOInj2 b ω : otval ω -> ectx (fun e => <{ ~inj@b<ω> e }>)
| CtxCase e1 e2: ectx (fun e0 => <{ case e0 of e1 | e2 }>)
| CtxOCase e1 e2: ectx (fun e0 => <{ ~case e0 of e1 | e2 }>)
| CtxFold X : ectx (fun e => <{ fold<X> e }>)
| CtxUnfold X : ectx (fun e => <{ unfold<X> e }>)
| CtxTape : ectx (fun e => <{ tape e }>)
| CtxMux1 e1 e2 : ectx (fun e0 => <{ mux e0 e1 e2 }>)
| CtxMux2 v0 e2 : wval v0 -> ectx (fun e1 => <{ mux v0 e1 e2 }>)
| CtxMux3 v0 v1 : wval v0 -> wval v1 -> ectx (fun e2 => <{ mux v0 v1 e2 }>)
(* NOTE: Extensions *)
| CtxIntLe1 l e2 : ectx (fun e1 => <{ e1 <={l} e2 }>)
| CtxIntLe2 l v1 : wval v1 -> ectx (fun e2 => <{ v1 <={l} e2 }>)
| CtxIntSec : ectx (fun e => <{ s_int e }>)
| CtxIntRet : ectx (fun e => <{ r_int e}>)
.

Variant lectx : (expr -> expr) -> Prop :=
| LCtxApp v2 : wval v2 -> lectx (fun e1 => <{ e1 v2 }>)
| LCtxSec : lectx (fun e => <{ s𝔹 e }>)
| LCtxIte e1 e2 : lectx (fun e0 => <{ if e0 then e1 else e2 }>)
| LCtxProj b : lectx (fun e => <{ π@b e }>)
| LCtxCase e1 e2: lectx (fun e0 => <{ case e0 of e1 | e2 }>)
| LCtxUnfold X : lectx (fun e => <{ unfold<X> e }>)
(* NOTE: Extensions *)
| LCtxIntSec : lectx (fun e => <{ s_int e }>)
| LCtxIntLe1 v2 : wval v2 -> lectx (fun e1 => <{ e1 <= v2 }>)
| LCtxIntLe2 n : lectx (fun e => <{ i(n) <= e }>)
.

(** ** Small-step relation *)
Section step.

Context (Σ : gctx).

Reserved Notation "e '-->!' e'" (at level 40).

Inductive step : expr -> expr -> Prop :=
| SApp l τ e v :
    wval v ->
    <{ (\:{l}τ => e) v }> -->! <{ e^v }>
| STApp X τ e v :
    wval v ->
    Σ !! X = Some (DOADT τ e) ->
    <{ (gvar X) v }> -->! <{ e^v }>
| SFun x T e :
    Σ !! x = Some (DFun T e) ->
    <{ gvar x }> -->! <{ e }>
| SLet v e :
    wval v ->
    <{ let v in e }> -->! <{ e^v }>
| SSec b :
    <{ s𝔹 b }> -->! <{ [b] }>
| SIte b e1 e2 :
    <{ if b then e1 else e2 }> -->! <{ ite b e1 e2 }>
| SProj b v1 v2 :
    wval v1 -> wval v2 ->
    <{ π@b (v1, v2) }> -->! <{ ite b v1 v2 }>
| SOInj b ω v :
    otval ω -> oval v ->
    <{ ~inj@b<ω> v }> -->! <{ [inj@b<ω> v] }>
| SCase b τ v e1 e2 :
    wval v ->
    <{ case inj@b<τ> v of e1 | e2 }> -->! <{ ite b (e1^v) (e2^v) }>
| SOCase b ω1 ω2 v e1 e2 v1 v2 :
    oval v ->
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> -->!
      <{ ~if [b] then (ite b (e1^v) (e1^v1)) else (ite b (e2^v2) (e2^v)) }>
| SUnfold X X' v :
    wval v ->
    <{ unfold<X> (fold <X'> v) }> -->! v
| SMux b v1 v2 :
    wval v1 -> wval v2 ->
    <{ mux [b] v1 v2 }> -->! <{ ite b v1 v2 }>
| STapeOIte b v1 v2 :
    woval v1 -> woval v2 ->
    <{ tape (~if [b] then v1 else v2) }> -->! <{ mux [b] (tape v1) (tape v2) }>
| STapePair v1 v2 :
    woval v1 -> woval v2 ->
    <{ tape (v1, v2) }> -->! <{ (tape v1, tape v2) }>
| STapeUnitV :
    <{ tape () }> -->! <{ () }>
| STapeBoxedLit b :
    <{ tape [b] }> -->! <{ [b] }>
| STapeBoxedInj b ω v :
    otval ω -> oval v ->
    <{ tape [inj@b<ω> v] }> -->! <{ [inj@b<ω> v] }>
(* NOTE: Extensions *)
| SIntLe m n : <{ i(m) <= i(n) }> -->! <{ lit (leb m n) }>
| SOIntLe m n : <{ i[m] ~<= i[n] }> -->! <{ [leb m n] }>
| SIntSec n : <{ s_int i(n) }> -->! <{ i[n] }>
| SIntSecRet n : <{ s_int (r_int i[n]) }> -->! <{ i[n] }>
| SIntRetLe1 m n : <{ r_int i[m] <= r_int i[n] }> -->! <{ r𝔹 (i[m] ~<= i[n]) }>
| SIntRetLe2 m n : <{ r_int i[m] <= i(n) }> -->! <{ r𝔹 (i[m] ~<= s_int i(n)) }>
| SIntRetLe3 m n : <{ i(m) <= r_int i[n] }> -->! <{ r𝔹 (s_int i(m) ~<= i[n]) }>
| STapeOInt n : <{ tape i[n] }> -->! <{ i[n] }>

(* Keep these two rules at the end for convenience. *)
| SOIte b v1 v2 ℇ :
    lectx ℇ ->
    wval v1 -> wval v2 ->
    ℇ <{ ~if [b] then v1 else v2 }> -->! <{ ~if [b] then ,(ℇ v1) else ,(ℇ v2) }>
| SCtx ℇ e e' :
    ectx ℇ ->
    e -->! e' ->
    ℇ e -->! ℇ e'

where "e '-->!' e'" := (step e e').

End step.

Module semantics_notations.

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

End semantics_notations.

Import semantics_notations.

(** * Typing *)

(** ** Typing context (Γ) *)
Notation tctx := (amap lexpr).

Section typing.

Import kind_notations.

Section fix_gctx.

Context (Σ : gctx).

(** ** Parallel reduction *)
Reserved Notation "e '==>!' e'" (at level 40,
                                 e' constr at level 0).

(** We do not extend the parallel reduction, which means primitive integers are
not used in type level. While we can certainly do that, our demos currently do
not need this feature. *)
Inductive pared : expr -> expr -> Prop :=
| RApp l τ e1 e2 e1' e2' L :
    e1 ==>! e1' ->
    (forall x, x ∉ L -> <{ e2^x }> ==>! <{ e2'^x }>) ->
    lc τ ->
    <{ (\:{l}τ => e2) e1 }> ==>! <{ e2'^e1' }>
| ROADT X τ' τ e e' :
    Σ !! X = Some (DOADT τ' τ) ->
    e ==>! e' ->
    <{ (gvar X) e }> ==>! <{ τ^e' }>
| RLet e1 e2 e1' e2' L :
    e1 ==>! e1' ->
    (forall x, x ∉ L -> <{ e2^x }> ==>! <{ e2'^x }>) ->
    <{ let e1 in e2 }> ==>! <{ e2'^e1' }>
| RFun x T e :
    Σ !! x = Some (DFun T e) ->
    <{ gvar x }> ==>! <{ e }>
| RProj b e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ π@b (e1, e2) }> ==>! <{ ite b e1' e2' }>
| RFold X X' e e' :
    e ==>! e' ->
    <{ unfold<X> (fold<X'> e) }> ==>! e'
| RIte b e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ if b then e1 else e2 }> ==>! <{ ite b e1' e2' }>
| RCase b τ e0 e1 e2 e0' e1' e2' L1 L2 :
    e0 ==>! e0' ->
    (forall x, x ∉ L1 -> <{ e1^x }> ==>! <{ e1'^x }>) ->
    (forall x, x ∉ L2 -> <{ e2^x }> ==>! <{ e2'^x }>) ->
    lc τ ->
    <{ case inj@b<τ> e0 of e1 | e2 }> ==>! <{ ite b (e1'^e0') (e2'^e0') }>
| RMux b e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ mux [b] e1 e2 }> ==>! <{ ite b e1' e2' }>
| ROIte b e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ ~if [b] then e1 else e2 }> ==>! <{ ite b e1' e2' }>
| ROCase b ω1 ω2 v v1 v2 e1 e2 e1' e2' L1 L2 :
    oval v ->
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    (forall x, x ∉ L1 -> <{ e1^x }> ==>! <{ e1'^x }>) ->
    (forall x, x ∉ L2 -> <{ e2^x }> ==>! <{ e2'^x }>) ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> ==>!
      <{ ~if [b] then (ite b (e1'^v) (e1'^v1)) else (ite b (e2'^v2) (e2'^v)) }>
| RSec b :
    <{ s𝔹 b }> ==>! <{ [b] }>
| ROInj b ω v :
    otval ω -> oval v ->
    <{ ~inj@b<ω> v }> ==>! <{ [inj@b<ω> v] }>
| ROIteApp b e1 e2 e e1' e2' e' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    e ==>! e' ->
    <{ (~if [b] then e1 else e2) e }> ==>! <{ ~if [b] then e1' e' else e2' e' }>
| ROIteSec b e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ s𝔹 (~if [b] then e1 else e2) }> ==>! <{ ~if [b] then s𝔹 e1' else s𝔹 e2' }>
| ROIteIte b e1 e2 e3 e4 e1' e2' e3' e4' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    e3 ==>! e3' ->
    e4 ==>! e4' ->
    <{ if (~if [b] then e1 else e2) then e3 else e4 }> ==>!
      <{ ~if [b] then (if e1' then e3' else e4') else (if e2' then e3' else e4') }>
| ROIteProj b b' e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ π@b' (~if [b] then e1 else e2) }> ==>!
      <{ ~if [b] then π@b' e1' else π@b' e2' }>
| ROIteCase b e1 e2 e3 e4 e1' e2' e3' e4' L1 L2 :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    (forall x, x ∉ L1 -> <{ e3^x }> ==>! <{ e3'^x }>) ->
    (forall x, x ∉ L2 -> <{ e4^x }> ==>! <{ e4'^x }>) ->
    <{ case (~if [b] then e1 else e2) of e3 | e4 }> ==>!
      <{ ~if [b] then (case e1' of e3' | e4') else (case e2' of e3' | e4') }>
| ROIteUnfold X b e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ unfold<X> (~if [b] then e1 else e2) }> ==>!
      <{ ~if [b] then unfold<X> e1' else unfold<X> e2' }>
| RTapeOIte b e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ tape (~if [b] then e1 else e2) }> ==>! <{ mux [b] (tape e1') (tape e2') }>
| RTapePair e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    woval e1 -> woval e2 ->
    <{ tape (e1, e2) }> ==>! <{ (tape e1', tape e2') }>
| RTapeUnitV :
    <{ tape () }> ==>! <{ () }>
| RTapeBoxedLit b :
    <{ tape [b] }> ==>! <{ [b] }>
| RTapeBoxedInj b ω v :
    otval ω -> oval v ->
    <{ tape [inj@b<ω> v] }> ==>! <{ [inj@b<ω> v] }>
| RCgrPi l τ1 τ2 τ1' τ2' L :
    τ1 ==>! τ1' ->
    (forall x, x ∉ L -> <{ τ2^x }> ==>! <{ τ2'^x }>) ->
    <{ Π:{l}τ1, τ2 }> ==>! <{ Π:{l}τ1', τ2' }>
| RCgrAbs l τ e τ' e' L :
    τ ==>! τ' ->
    (forall x, x ∉ L -> <{ e^x }> ==>! <{ e'^x }>) ->
    <{ \:{l}τ => e }> ==>! <{ \:{l}τ' => e' }>
| RCgrApp e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ e1 e2 }> ==>! <{ e1' e2' }>
| RCgrLet e1 e2 e1' e2' L :
    e1 ==>! e1' ->
    (forall x, x ∉ L -> <{ e2^x }> ==>! <{ e2'^x }>) ->
    <{ let e1 in e2 }> ==>! <{ let e1' in e2' }>
| RCgrSec e e' :
    e ==>! e' ->
    <{ s𝔹 e }> ==>! <{ s𝔹 e' }>
| RCgrIte l e0 e1 e2 e0' e1' e2' :
    e0 ==>! e0' ->
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ if{l} e0 then e1 else e2 }> ==>! <{ if{l} e0' then e1' else e2' }>
| RCgrProd τ1 τ2 τ1' τ2' :
    τ1 ==>! τ1' ->
    τ2 ==>! τ2' ->
    <{ τ1 * τ2 }> ==>! <{ τ1' * τ2' }>
| RCgrPair e1 e2 e1' e2' :
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ (e1, e2) }> ==>! <{ (e1', e2') }>
| RCgrProj b e e' :
    e ==>! e' ->
    <{ π@b e }> ==>! <{ π@b e' }>
| RCgrSum l τ1 τ2 τ1' τ2' :
    τ1 ==>! τ1' ->
    τ2 ==>! τ2' ->
    <{ τ1 +{l} τ2 }> ==>! <{ τ1' +{l} τ2' }>
| RCgrInj l b τ e τ' e' :
    e ==>! e' ->
    τ ==>! τ' ->
    <{ inj{l}@b<τ> e }> ==>! <{ inj{l}@b<τ'> e' }>
| RCgrCase l e0 e1 e2 e0' e1' e2' L1 L2 :
    e0 ==>! e0' ->
    (forall x, x ∉ L1 -> <{ e1^x }> ==>! <{ e1'^x }>) ->
    (forall x, x ∉ L2 -> <{ e2^x }> ==>! <{ e2'^x }>) ->
    <{ case{l} e0 of e1 | e2 }> ==>! <{ case{l} e0' of e1' | e2' }>
| RCgrFold X e e' :
    e ==>! e' ->
    <{ fold<X> e }> ==>! <{ fold<X> e' }>
| RCgrUnfold X e e' :
    e ==>! e' ->
    <{ unfold<X> e }> ==>! <{ unfold<X> e' }>
| RCgrMux e0 e1 e2 e0' e1' e2' :
    e0 ==>! e0' ->
    e1 ==>! e1' ->
    e2 ==>! e2' ->
    <{ mux e0 e1 e2 }> ==>! <{ mux e0' e1' e2' }>
| RCgrTape e e' :
    e ==>! e' ->
    <{ tape e }> ==>! <{ tape e' }>
| RRefl e :
    lc e ->
    e ==>! e

where "e1 '==>!' e2" := (pared e1 e2)
.

(** ** Expression equivalence *)
Inductive pared_equiv : expr -> expr -> Prop :=
| QRRefl e : e ≡ e
| QRRedL e1 e1' e2 :
    e1 ==>! e1' ->
    e1' ≡ e2 ->
    e1 ≡ e2
| QRRedR e1 e2 e2' :
    e2 ==>! e2' ->
    e1 ≡ e2' ->
    e1 ≡ e2

where "e ≡ e'" := (pared_equiv e e')
.

(** ** Typing and kinding *)
Reserved Notation "Γ '⊢' e ':{' l '}' τ" (at level 40,
                                          e custom oadt at level 99,
                                          l constr at level 99,
                                          τ custom oadt at level 99).
Reserved Notation "Γ '⊢' τ '::' κ" (at level 40,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

Inductive typing : tctx -> expr -> bool -> expr -> Prop :=
| TFVar Γ x l τ κ :
    Γ !! x = Some (l, τ) ->
    Γ ⊢ τ :: κ ->
    Γ ⊢ fvar x :{l} τ
| TGVar Γ x l τ e :
    Σ !! x = Some (DFun (l, τ) e) ->
    Γ ⊢ gvar x :{l} τ
| TAbs Γ l1 l2 e τ1 τ2 κ L :
    (forall x, x ∉ L -> <[x:=(l2, τ2)]>Γ ⊢ e^x :{l1} τ1^x) ->
    Γ ⊢ τ2 :: κ ->
    Γ ⊢ \:{l2}τ2 => e :{l1} (Π:{l2}τ2, τ1)
| TLet Γ l1 l2 l e1 e2 τ1 τ2 L :
    Γ ⊢ e1 :{l1} τ1 ->
    (forall x, x ∉ L -> <[x:=(l1, τ1)]>Γ ⊢ e2^x :{l2} τ2^x) ->
    l = l1 ⊔ l2 ->
    Γ ⊢ let e1 in e2 :{l} τ2^e1
| TApp Γ l1 l2 e1 e2 τ1 τ2 :
    Γ ⊢ e1 :{l1} (Π:{l2}τ2, τ1) ->
    Γ ⊢ e2 :{l2} τ2 ->
    Γ ⊢ e1 e2 :{l1} τ1^e2
| TUnit Γ : Γ ⊢ () :{⊥} 𝟙
| TLit Γ b : Γ ⊢ lit b :{⊥} 𝔹
| TSec Γ l e :
    Γ ⊢ e :{l} 𝔹 ->
    Γ ⊢ s𝔹 e :{l} ~𝔹
| TIte Γ l1 l2 l e0 e1 e2 τ κ :
    Γ ⊢ e0 :{⊥} 𝔹 ->
    Γ ⊢ e1 :{l1} τ^(lit true) ->
    Γ ⊢ e2 :{l2} τ^(lit false) ->
    Γ ⊢ τ^e0 :: κ ->
    l = l1 ⊔ l2 ->
    Γ ⊢ if e0 then e1 else e2 :{l} τ^e0
| TIteNoDep Γ l0 l1 l2 l e0 e1 e2 τ :
    Γ ⊢ e0 :{l0} 𝔹 ->
    Γ ⊢ e1 :{l1} τ ->
    Γ ⊢ e2 :{l2} τ ->
    l = l0 ⊔ l1 ⊔ l2 ->
    Γ ⊢ if e0 then e1 else e2 :{l} τ
| TOIte Γ l1 l2 e0 e1 e2 τ κ :
    Γ ⊢ e0 :{⊥} ~𝔹 ->
    Γ ⊢ e1 :{l1} τ ->
    Γ ⊢ e2 :{l2} τ ->
    Γ ⊢ τ :: κ ->
    Γ ⊢ ~if e0 then e1 else e2 :{⊤} τ
| TInj Γ l b e τ1 τ2 κ :
    Γ ⊢ e :{l} ite b τ1 τ2 ->
    Γ ⊢ τ1 + τ2 :: κ ->
    Γ ⊢ inj@b<τ1 + τ2> e :{l} τ1 + τ2
| TOInj Γ b e τ1 τ2 :
    Γ ⊢ e :{⊥} ite b τ1 τ2 ->
    Γ ⊢ τ1 ~+ τ2 :: *@O ->
    Γ ⊢ ~inj@b<τ1 ~+ τ2> e :{⊥} τ1 ~+ τ2
| TCase Γ l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 :
    Γ ⊢ e0 :{⊥} τ1 + τ2 ->
    (forall x, x ∉ L1 -> <[x:=(⊥, τ1)]>Γ ⊢ e1^x :{l1} τ^(inl<τ1 + τ2> x)) ->
    (forall x, x ∉ L2 -> <[x:=(⊥, τ2)]>Γ ⊢ e2^x :{l2} τ^(inr<τ1 + τ2> x)) ->
    Γ ⊢ τ^e0 :: κ ->
    l = l1 ⊔ l2 ->
    Γ ⊢ case e0 of e1 | e2 :{l} τ^e0
| TCaseNoDep Γ l0 l1 l2 l e0 e1 e2 τ1 τ2 τ κ L1 L2 :
    Γ ⊢ e0 :{l0} τ1 + τ2 ->
    (forall x, x ∉ L1 -> <[x:=(l0, τ1)]>Γ ⊢ e1^x :{l1} τ) ->
    (forall x, x ∉ L2 -> <[x:=(l0, τ2)]>Γ ⊢ e2^x :{l2} τ) ->
    Γ ⊢ τ :: κ ->
    l = l0 ⊔ l1 ⊔ l2 ->
    Γ ⊢ case e0 of e1 | e2 :{l} τ
| TOCase Γ l1 l2 e0 e1 e2 τ1 τ2 τ κ L1 L2 :
    Γ ⊢ e0 :{⊥} τ1 ~+ τ2 ->
    (forall x, x ∉ L1 -> <[x:=(⊥, τ1)]>Γ ⊢ e1^x :{l1} τ) ->
    (forall x, x ∉ L2 -> <[x:=(⊥, τ2)]>Γ ⊢ e2^x :{l2} τ) ->
    Γ ⊢ τ :: κ ->
    Γ ⊢ ~case e0 of e1 | e2 :{⊤} τ
| TPair Γ l1 l2 l e1 e2 τ1 τ2 :
    Γ ⊢ e1 :{l1} τ1 ->
    Γ ⊢ e2 :{l2} τ2 ->
    l = l1 ⊔ l2 ->
    Γ ⊢ (e1, e2) :{l} τ1 * τ2
| TProj Γ l b e τ1 τ2 :
    Γ ⊢ e :{l} τ1 * τ2 ->
    Γ ⊢ π@b e :{l} ite b τ1 τ2
| TFold Γ l X e τ :
    Σ !! X = Some (DADT τ) ->
    Γ ⊢ e :{l} τ ->
    Γ ⊢ fold<X> e :{l} gvar X
| TUnfold Γ l X e τ :
    Σ !! X = Some (DADT τ) ->
    Γ ⊢ e :{l} gvar X ->
    Γ ⊢ unfold<X> e :{l} τ
| TMux Γ e0 e1 e2 τ :
    Γ ⊢ e0 :{⊥} ~𝔹 ->
    Γ ⊢ e1 :{⊥} τ ->
    Γ ⊢ e2 :{⊥} τ ->
    Γ ⊢ τ :: *@O ->
    Γ ⊢ mux e0 e1 e2 :{⊥} τ
| TTape Γ l e τ :
    Γ ⊢ e :{l} τ ->
    Γ ⊢ τ :: *@O ->
    Γ ⊢ tape e :{⊥} τ
| TBoxedLit Γ b : Γ ⊢ [b] :{⊥} ~𝔹
| TBoxedInj Γ b v ω :
    ovalty <{ [inj@b<ω> v] }> ω ->
    Γ ⊢ [inj@b<ω> v] :{⊥} ω
(* NOTE: Extensions *)
| TIntLit Γ n :
  Γ ⊢ i(n) :{⊥} int
| TIntLe Γ l1 l2 l m n :
    Γ ⊢ m :{l1} int ->
    Γ ⊢ n :{l2} int ->
    l = l1 ⊔ l2 ->
    Γ ⊢ m <= n :{l} 𝔹
| TOIntLe Γ m n :
    Γ ⊢ m :{⊥} ~int ->
    Γ ⊢ n :{⊥} ~int ->
    Γ ⊢ m ~<= n :{⊥} ~𝔹
| TIntSec Γ l n :
    Γ ⊢ n :{l} int ->
    Γ ⊢ s_int n :{l} ~int
| TIntRet Γ n :
    Γ ⊢ n :{⊥} ~int ->
    Γ ⊢ r_int n :{⊤} int
| TIntBoxedLit Γ n :
  Γ ⊢ i[n] :{⊥} ~int

(* We still keep the type conversion rule at the end. *)
| TConv Γ l l' e τ τ' κ :
    Γ ⊢ e :{l'} τ' ->
    τ' ≡ τ ->
    Γ ⊢ τ :: κ ->
    l' ⊑ l ->
    Γ ⊢ e :{l} τ

with kinding : tctx -> expr -> kind -> Prop :=
| KVarADT Γ X τ :
    Σ !! X = Some (DADT τ) ->
    Γ ⊢ gvar X :: *@P
| KUnit Γ : Γ ⊢ 𝟙 :: *@A
| KBool Γ l : Γ ⊢ 𝔹{l} :: ite l *@O *@P
| KPi Γ l τ1 τ2 κ1 κ2 L :
    (forall x, x ∉ L -> <[x:=(l, τ1)]>Γ ⊢ τ2^x :: κ2) ->
    Γ ⊢ τ1 :: κ1 ->
    Γ ⊢ (Π:{l}τ1, τ2) :: *@M
| KApp Γ e' e τ X :
    Σ !! X = Some (DOADT τ e') ->
    Γ ⊢ e :{⊥} τ ->
    Γ ⊢ (gvar X) e :: *@O
| KProd Γ τ1 τ2 κ :
    Γ ⊢ τ1 :: κ ->
    Γ ⊢ τ2 :: κ ->
    Γ ⊢ τ1 * τ2 :: κ
| KSum Γ τ1 τ2 κ :
    Γ ⊢ τ1 :: κ ->
    Γ ⊢ τ2 :: κ ->
    Γ ⊢ τ1 + τ2 :: (κ ⊔ *@P)
| KOSum Γ τ1 τ2 :
    Γ ⊢ τ1 :: *@O ->
    Γ ⊢ τ2 :: *@O ->
    Γ ⊢ τ1 ~+ τ2 :: *@O
| KIte Γ e0 τ1 τ2 :
    Γ ⊢ e0 :{⊥} 𝔹 ->
    Γ ⊢ τ1 :: *@O ->
    Γ ⊢ τ2 :: *@O ->
    Γ ⊢ if e0 then τ1 else τ2 :: *@O
| KCase Γ e0 τ1 τ2 τ1' τ2' L1 L2 :
    Γ ⊢ e0 :{⊥} τ1' + τ2' ->
    (forall x, x ∉ L1 -> <[x:=(⊥, τ1')]>Γ ⊢ τ1^x :: *@O) ->
    (forall x, x ∉ L2 -> <[x:=(⊥, τ2')]>Γ ⊢ τ2^x :: *@O) ->
    Γ ⊢ case e0 of τ1 | τ2 :: *@O
| KLet Γ e τ τ' L :
    Γ ⊢ e :{⊥} τ' ->
    (forall x, x ∉ L -> <[x:=(⊥, τ')]>Γ ⊢ τ^x :: *@O) ->
    Γ ⊢ let e in τ :: *@O
(* NOTE: Extensions *)
| KInt Γ l : Γ ⊢ int{l} :: ite l *@O *@P

(* We still keep the subsumption rule at the end. *)
| KSub Γ τ κ κ' :
    Γ ⊢ τ :: κ' ->
    κ' ⊑ κ ->
    Γ ⊢ τ :: κ

where "Γ '⊢' e ':{' l '}' τ" := (typing Γ e l τ)
  and "Γ '⊢' τ '::' κ" := (kinding Γ τ κ)
.

End fix_gctx.

(** Better induction principle. *)
Scheme typing_kinding_ind := Minimality for typing Sort Prop
  with kinding_typing_ind := Minimality for kinding Sort Prop.
Combined Scheme typing_kinding_mutind
         from typing_kinding_ind, kinding_typing_ind.

Notation "Σ '⊢' e '≡' e'" := (pared_equiv Σ e e')
                               (at level 40,
                                e custom oadt at level 99,
                                e' custom oadt at level 99).
Notation "Σ ; Γ '⊢' e ':{' l '}' τ" := (typing Σ Γ e l τ)
                                         (at level 40,
                                          Γ constr at level 0,
                                          e custom oadt at level 99,
                                          τ custom oadt at level 99,
                                          format "Σ ;  Γ  '⊢'  e  ':{' l '}'  τ").
Notation "Σ ; Γ '⊢' τ '::' κ" := (kinding Σ Γ τ κ)
                                   (at level 40,
                                    Γ constr at level 0,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

(** ** Global definitions typing *)
Reserved Notation "Σ '⊢₁' D" (at level 40,
                               D constr at level 0).

Inductive gdef_typing : gctx -> gdef -> Prop :=
| TADT Σ τ :
    Σ; ∅ ⊢ τ :: *@P ->
    Σ ⊢₁ (DADT τ)
| TOADT Σ τ e L :
    Σ; ∅ ⊢ τ :: *@P ->
    (forall x, x ∉ L -> Σ; ({[x:=(⊥, τ)]}) ⊢ e^x :: *@O) ->
    Σ ⊢₁ (DOADT τ e)
| TFun Σ l τ e κ :
    Σ; ∅ ⊢ τ :: κ ->
    Σ; ∅ ⊢ e :{l} τ ->
    Σ ⊢₁ (DFun (l, τ) e)

where "Σ '⊢₁' D" := (gdef_typing Σ D)
.

Definition gctx_typing (Σ : gctx) : Prop :=
  map_Forall (fun _ D => Σ ⊢₁ D) Σ.

(** ** Program typing *)
Definition program_typing (Σ : gctx) (e : expr) (τ : expr) :=
  gctx_typing Σ /\ Σ; ∅ ⊢ e :{⊥} τ.

End typing.

Module typing_notations.

Export kind_notations.

Notation "Σ '⊢' e '==>!' e'" := (pared Σ e e')
                                  (at level 40,
                                   e custom oadt at level 99,
                                   e' custom oadt at level 99).
Notation "Σ '⊢' e '==>*' e'" := (rtc (pared Σ) e e')
                                  (at level 40,
                                   e custom oadt at level 99,
                                   e' custom oadt at level 99).
Notation "Σ '⊢' e '≡' e'" := (pared_equiv Σ e e')
                               (at level 40,
                                e custom oadt at level 99,
                                e' custom oadt at level 99).

Notation "Σ ; Γ '⊢' e ':{' l '}' τ" := (typing Σ Γ e l τ)
                                         (at level 40,
                                          Γ constr at level 0,
                                          e custom oadt at level 99,
                                          l constr at level 99,
                                          τ custom oadt at level 99,
                                          format "Σ ;  Γ  '⊢'  e  ':{' l '}'  τ").
Notation "Σ ; Γ '⊢' e ':' τ" := (typing Σ Γ e _ τ)
                                         (at level 40,
                                          Γ constr at level 0,
                                          e custom oadt at level 99,
                                          τ custom oadt at level 99,
                                          only parsing).
Notation "Σ ; Γ '⊢' τ '::' κ" := (kinding Σ Γ τ κ)
                                   (at level 40,
                                    Γ constr at level 0,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

Notation "Σ '⊢₁' D" := (gdef_typing Σ D) (at level 40,
                                          D constr at level 0).

Notation "Σ ; e '▷' τ" := (program_typing Σ e τ)
                            (at level 40,
                             e constr at level 0,
                             τ constr at level 0).

End typing_notations.

Import typing_notations.

#[local]
Set Default Proof Using "Type".

(** We only prove the lemmas needed for the demos. *)

(** * Infrastructure *)

(** ** Body of local closure *)
Definition body (e : expr) : Prop :=
  exists L, forall x, x ∉ L -> lc <{ e^x }>.

(** ** Variable closing *)
Section close.

Reserved Notation "'{' k '<~' x '}' e" (in custom oadt at level 20, k constr).

Fixpoint close_ (k : nat) (x : atom) (e : expr) : expr :=
  match e with
  | <{ fvar y }> => if decide (x = y) then <{ bvar k }> else e
  | <{ Π:{l}τ1, τ2 }> => <{ Π:{l}({k<~x}τ1), {S k<~x}τ2 }>
  | <{ \:{l}τ => e }> => <{ \:{l}({k<~x}τ) => {S k<~x}e }>
  | <{ let e1 in e2 }> => <{ let {k<~x}e1 in {S k<~x}e2 }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {k<~x}e0 of {S k<~x}e1 | {S k<~x}e2 }>
  (* Congruence rules *)
  | <{ e1 e2 }> => <{ ({k<~x}e1) ({k<~x}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({k<~x}e) }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} {k<~x}e0 then {k<~x}e1 else {k<~x}e2 }>
  | <{ τ1 * τ2 }> => <{ ({k<~x}τ1) * ({k<~x}τ2) }>
  | <{ (e1, e2) }> => <{ ({k<~x}e1, {k<~x}e2) }>
  | <{ π@b e }> => <{ π@b ({k<~x}e) }>
  | <{ τ1 +{l} τ2 }> => <{ ({k<~x}τ1) +{l} ({k<~x}τ2) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({k<~x}τ)> ({k<~x}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({k<~x}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({k<~x}e) }>
  | <{ mux e0 e1 e2 }> => <{ mux ({k<~x}e0) ({k<~x}e1) ({k<~x}e2) }>
  | <{ tape e }> => <{ tape ({k<~x}e) }>
  (* NOTE: Extensions *)
  | <{ e1 <={l} e2 }> => <{ ({k<~x}e1) <={l} ({k<~x}e2) }>
  | <{ s_int e }> => <{ s_int ({k<~x}e) }>
  | <{ r_int e }> => <{ r_int ({k<~x}e) }>
  | _ => e
  end

where "'{' k '<~' x '}' e" := (close_ k x e) (in custom oadt).

End close.

Definition close x e := close_ 0 x e.

(** ** Free variables *)
Fixpoint fv (e : expr) : aset :=
  match e with
  | <{ fvar x }> => {[x]}
  (* Congruence rules *)
  | <{ \:{_}τ => e }> | <{ inj{_}@_<τ> e }> | <{ [inj@_<τ> e] }> =>
    fv τ ∪ fv e
  | <{ Π:{_}τ1, τ2 }> | <{ τ1 * τ2 }> | <{ τ1 +{_} τ2 }> =>
    fv τ1 ∪ fv τ2
  | <{ let e1 in e2 }> | <{ (e1, e2) }> | <{ e1 e2 }> =>
    fv e1 ∪ fv e2
  | <{ case{_} e0 of e1 | e2 }> | <{ if{_} e0 then e1 else e2 }>
  | <{ mux e0 e1 e2 }> =>
    fv e0 ∪ fv e1 ∪ fv e2
  | <{ s𝔹 e }> | <{ π@_ e }>
  | <{ fold<_> e }> | <{ unfold<_> e }>
  | <{ tape e }> =>
    fv e
  (* NOTE: Extensions *)
  | <{ e1 <={l} e2 }> => fv e1 ∪ fv e2
  | <{ s_int e }> | <{ r_int e }> => fv e
  | _ => ∅
  end.

Instance atom_stale : @Stale aset atom := singleton.
Arguments atom_stale /.

Instance aset_stale : Stale aset := id.
Arguments aset_stale /.

Instance expr_stale : Stale expr := fv.
Arguments expr_stale /.

(** We do not need the variables to be fresh against the range of typing
context. *)
Instance tctx_stale : Stale tctx := fun Γ => dom aset Γ.
Arguments tctx_stale /.

Arguments stale /.

(** ** Tactics *)
Ltac case_label :=
  let go l := (is_var l; destruct l) in
  match goal with
  | |- context [<{ if{?l} _ then _ else _ }>] => go l
  | |- context [<{ inj{?l}@_<_> _ }>] => go l
  | |- context [<{ case{?l} _ of _ | _ }>] => go l
  | |- context [<{ 𝔹{?l} }>] => go l
  | |- context [<{ _ +{?l} _ }>] => go l
  (* NOTE: Extensions *)
  | |- context [<{ int{?l} }>] => go l
  | |- context [<{ _ <={?l} _ }>] => go l
  end.

Ltac safe_inv e H := head_constructor e; sinvert H; simplify_eq.
Ltac safe_inv1 R :=
  match goal with
  | H : R ?e |- _ => safe_inv e H
  end.

Ltac wval_inv := safe_inv1 wval.

Ltac woval_inv := safe_inv1 woval.

Lemma SCtx_intro Σ ℇ e e' E E' :
    Σ ⊨ e -->! e' ->
    ℇ e = E ->
    ℇ e' = E' ->
    ectx ℇ ->
    Σ ⊨ E -->! E'.
Proof.
  hauto ctrs: step.
Qed.

Ltac solve_ectx :=
  let go H :=
    eapply SCtx_intro;
    [ solve [apply H; eauto]
    | higher_order_reflexivity
    | higher_order_reflexivity
    | solve [constructor; eauto; constructor; eauto] ]
  in match goal with
     | H : _ ⊨ _ -->! _ |- _ ⊨ _ -->! _ => go H
     | H : context [ _ -> _ ⊨ _ -->! _ ] |- _ ⊨ _ -->! _ => go H
     end.

Ltac apply_SOIte :=
  match goal with
  | |- _ ⊨ ?e -->! _ =>
    match e with
    | context E [<{ ~if ?b then ?v1 else ?v2 }>] =>
      let ℇ' := constr:(fun t : expr =>
                 ltac:(let t := context E [t] in exact t)) in
      apply SOIte with (ℇ := ℇ')
    end
  end.

Ltac solve_lctx := apply_SOIte; eauto using lectx.
Ltac solve_ctx := solve [ solve_lctx | solve_ectx ].

Ltac relax_typing_type :=
  match goal with
  | |- ?Σ; ?Γ ⊢ ?e :{?l} _ =>
    refine (eq_ind _ (fun τ => Σ; Γ ⊢ e :{l} τ) _ _ _)
  end.

Create HintDb lc discriminated.
#[export]
Hint Constructors lc : lc.

(** ** Lemmas *)
Lemma open_lc_ e : forall s u i j,
  <{ {j~>u}({i~>s}e) }> = <{ {i~>s}e }> ->
  i <> j ->
  <{ {j~>u}e }> = e.
Proof.
  induction e; hauto.
Qed.

Lemma open_lc e : forall s,
  lc e -> forall k, <{ {k~>s}e }> = e.
Proof.
  induction 1; try scongruence;
    simpl_cofin; hauto use: open_lc_.
Qed.

Lemma open_lc_intro e s :
  lc e -> <{ e^s }> = e.
Proof.
  unfold open.
  qauto use: open_lc.
Qed.

Lemma open_inj x e1 : forall e2,
  <{ e1^x }> = <{ e2^x }> ->
  x ∉ fv e1 ∪ fv e2 ->
  e1 = e2.
Proof.
  unfold open. generalize 0.
  induction e1; intros; subst; simpl in *;
  lazymatch goal with
  | H : ?e' = <{ {_~>_}?e }> |- _ =>
    destruct e; simpl in *; repeat (try scongruence; case_decide);
      try (head_constructor e'; sinvert H)
  end;
    repeat f_equal;
    try (auto_eapply; eauto; fast_set_solver!!).

  all: set_unfold; sfirstorder.
Qed.

Lemma open_close_ (x y z : atom) e : forall i j,
  i <> j ->
  y # e ->
  y <> x ->
  open_ i y (open_ j z (close_ j x e)) = open_ j z (close_ j x (open_ i y e)).
Proof.
  induction e; intros; simpl;
    solve [ repeat (case_decide; subst; simpl; try scongruence; eauto)
          | f_equal; auto_apply; eauto; fast_set_solver!! ].
Qed.

Lemma open_close e x :
  lc e ->
  open x (close x e) = e.
Proof.
  intros H.
  unfold open, close. generalize 0.
  induction H; intros; simpl; try hauto;
    f_equal; eauto;
      match goal with
      | |- ?e = _ => simpl_cofin (fv e)
      end;
      (eapply open_inj; [ unfold open; rewrite open_close_ | ]);
      eauto; fast_set_solver!!.
Qed.

Lemma ovalty_elim v ω:
  ovalty v ω ->
  oval v /\ otval ω /\ forall Σ Γ, Σ; Γ ⊢ v :{⊥} ω.
Proof.
  induction 1; hauto lq: on ctrs: oval, ovalty, otval, typing.
Qed.

Lemma otval_lc ω :
  otval ω ->
  lc ω.
Proof.
  induction 1; eauto with lc.
Qed.
#[export]
Hint Resolve otval_lc : lc.

Lemma ovalty_lc v ω :
  ovalty v ω ->
  lc v /\ lc ω.
Proof.
  induction 1; try hauto ctrs: lc.

  hauto use: otval_lc, ovalty_elim ctrs: otval, lc.
Qed.

Lemma ovalty_lc1 v ω :
  ovalty v ω ->
  lc v.
Proof.
  hauto use: ovalty_lc.
Qed.
#[export]
Hint Resolve ovalty_lc1 : lc.

Lemma ovalty_lc2 v ω :
  ovalty v ω ->
  lc ω.
Proof.
  hauto use: ovalty_lc.
Qed.
#[export]
Hint Resolve ovalty_lc2 : lc.

Lemma typing_lc Σ Γ e l τ :
  Σ; Γ ⊢ e :{l} τ ->
  lc e
with kinding_lc  Σ Γ τ κ :
  Σ; Γ ⊢ τ :: κ ->
  lc τ.
Proof.
  all : destruct 1; eauto with lc;
    econstructor; simpl_cofin; eauto with lc.
Qed.
#[export]
Hint Resolve typing_lc kinding_lc : lc.

Lemma typing_body Σ Γ e l τ T L :
  (forall x, x ∉ L -> Σ; (<[x:=T]>Γ) ⊢ e^x :{l} τ) ->
  body e.
Proof.
  intros. eexists. simpl_cofin.
  eauto using typing_lc.
Qed.
#[export]
Hint Resolve typing_body : lc.

Lemma kinding_body Σ Γ τ κ T L :
  (forall x, x ∉ L -> Σ; (<[x:=T]>Γ) ⊢ τ^x :: κ) ->
  body τ.
Proof.
  intros. eexists. simpl_cofin.
  eauto using kinding_lc.
Qed.
#[export]
Hint Resolve kinding_body : lc.

Lemma open_body e : forall s,
  body e -> forall k, k <> 0 -> <{ {k~>s}e }> = e.
Proof.
  unfold body.
  intros. simp_hyps.
  simpl_cofin.
  erewrite (open_lc_ _ x _ 0); eauto.
  by rewrite open_lc by assumption.
Qed.

Lemma pared_weakening Σ e e' :
  Σ ⊢ e ==>! e' ->
  forall Σ', Σ ⊆ Σ' ->
        Σ' ⊢ e ==>! e'.
Proof.
  induction 1; intros;
    econstructor; eauto using lookup_weaken.
Qed.

Lemma pared_equiv_weakening Σ e e' :
  Σ ⊢ e ≡ e' ->
  forall Σ', Σ ⊆ Σ' ->
        Σ' ⊢ e ≡ e'.
Proof.
  induction 1; intros; eauto using pared_equiv, pared_weakening.
Qed.

Lemma weakening_ Σ :
  (forall Γ e l τ,
    Σ; Γ ⊢ e :{l} τ ->
    forall Σ' Γ',
      Σ ⊆ Σ' ->
      Γ ⊆ Γ' ->
      Σ'; Γ' ⊢ e :{l} τ) /\
  (forall Γ τ κ,
    Σ; Γ ⊢ τ :: κ ->
    forall Σ' Γ',
      Σ ⊆ Σ' ->
      Γ ⊆ Γ' ->
      Σ'; Γ' ⊢ τ :: κ).
Proof.
  apply typing_kinding_mutind; intros; subst;
    try qauto l: on ctrs: typing, kinding;
    try qauto l: on use: lookup_weaken ctrs: typing, kinding;
    try qauto l: on use: insert_mono ctrs: typing, kinding;
    econstructor; eauto using insert_mono, pared_equiv_weakening.
Qed.

Lemma kinding_weakening Σ Γ Σ' Γ' τ κ :
  Σ; Γ ⊢ τ :: κ ->
  Σ ⊆ Σ' ->
  Γ ⊆ Γ' ->
  Σ'; Γ' ⊢ τ :: κ.
Proof.
  hauto use: weakening_.
Qed.

Lemma kinding_weakening_insert Σ Γ τ τ' κ x :
  Σ; Γ ⊢ τ :: κ ->
  x ∉ dom aset Γ ->
  Σ; (<[x:=τ']>Γ) ⊢ τ :: κ.
Proof.
  eauto using kinding_weakening, insert_fresh_subseteq.
Qed.

#[global]
Instance pared_equiv_is_symm Σ : Symmetric (pared_equiv Σ).
Proof.
  hnf; induction 1; eauto using pared_equiv.
Qed.

#[global]
Instance pared_equiv_is_refl Σ : Reflexive (pared_equiv Σ).
Proof.
  hnf; intros; econstructor.
Qed.


(** * Decision procedures *)

Section dec.

Ltac t :=
  solve [ repeat
            (try solve [ left; abstract (econstructor; assumption)
                       | right; abstract (inversion 1; subst; contradiction) ];
             try match reverse goal with
                 | H : sumbool _ _ |- _ => destruct H
                 end) ].

#[global]
Instance otval_dec ω : Decision (otval ω).
Proof.
  hnf. induction ω; try t; try case_label; try t.
Defined.

#[global]
Instance oval_dec v : Decision (oval v).
Proof.
  hnf. induction v; try t.

  match goal with
  | H : context [ oval ?ω ] |- context [<{ [inj@_<(?ω)> _] }>] =>
    clear H; destruct (decide (otval ω)); try t
  end.
Defined.

#[global]
Instance wval_dec v : Decision (wval v).
Proof.
  hnf. induction v; try t; try case_label; try t.
  - match goal with
    | H : context [ wval ?v] |- context [<{ ~if ?v then _ else _ }>] =>
      clear H; destruct v; try t
    end.
  - match goal with
    | H : context [ wval ?ω], H' : context [ wval ?v ] |-
      context [<{ [inj@_<(?ω)> ?v] }>] =>
      clear H; clear H';
        destruct (decide (otval ω)); try t;
        destruct (decide (oval v)); try t
    end.
  - match goal with
    | |- context [<{ r_int ?v }>] =>
      clear; destruct v; try t
    end.
Defined.

#[global]
Instance woval_dec v : Decision (woval v).
Proof.
  hnf. induction v; try t; try case_label; try t.
  - match goal with
    | H : context [ woval ?v] |- context [<{ ~if ?v then _ else _ }>] =>
      clear H; destruct v; try t
    end.
  - match goal with
    | H : context [ woval ?ω], H' : context [ woval ?v ] |-
      context [<{ [inj@_<(?ω)> ?v] }>] =>
      clear H; clear H';
        destruct (decide (otval ω)); try t;
        destruct (decide (oval v)); try t
    end.
Defined.

#[global]
Instance val_dec v : Decision (val v).
Proof.
  hnf. induction v; try t; try case_label; try t.
  match goal with
  | H : context [ val ?ω], H' : context [ val ?v ] |-
      context [<{ [inj@_<(?ω)> ?v] }>] =>
      clear H; clear H';
      destruct (decide (otval ω)); try t;
      destruct (decide (oval v)); try t
  end.
Defined.

End dec.


Section step.

Import Int63.

Context (Σ : gctx).

Fixpoint ovalty_ (ω : expr) : option expr :=
  match ω with
  | <{ 𝟙 }> => mret <{ () }>
  | <{ ~𝔹 }> => mret <{ [true] }>
  | <{ ω1 * ω2 }> => v1 <- ovalty_ ω1; v2 <- ovalty_ ω2; mret <{ (v1, v2) }>
  | <{ ω1 ~+ ω2 }> =>
      (* Notation clash *)
      mguard (otval ω2) (fun _ => v <- ovalty_ ω1; mret <{ [inl<ω1 ~+ ω2> v] }>)
  (* NOTE: Extensions *)
  | <{ ~int }> => mret <{ i[0] }>
  | _ => None
  end.

Fixpoint step_ (e : expr) : option expr :=
  match e with
  | <{ e1 e2 }> =>
    if decide (wval e2)
    then if decide (wval e1)
         then match e1 with
              | <{ \:{_}_ => e }> => mret <{ e^e2 }>
              | <{ ~if [b] then v1 else v2 }> =>
                  mret <{ ~if [b] then v1 e2 else v2 e2 }>
              | _ => None
              end
         else match e1 with
              | <{ gvar X }> =>
                  match Σ !! X with
                  | Some (DOADT _ e') => mret <{ e'^e2 }>
                  | _ => e1' <- step_ e1; mret <{ e1' e2 }>
                  end
              | _ => e1' <- step_ e1; mret <{ e1' e2 }>
              end
    else e2' <- step_ e2; mret <{ e1 e2' }>
  | <{ let e1 in e2 }> =>
    if decide (wval e1)
    then mret <{ e2^e1 }>
    else e1' <- step_ e1; mret <{ let e1' in e2 }>
  | <{ gvar x }> =>
    match Σ !! x with
    | Some (DFun _ e) => mret e
    | _ => None
    end
  | <{ s𝔹 e }> =>
    if decide (wval e)
    then match e with
         | <{ lit b }> => mret <{ [b] }>
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then s𝔹 v1 else s𝔹 v2 }>
         | _ => None
         end
    else e' <- step_ e; mret <{ s𝔹 e' }>
  | <{ if e0 then e1 else e2 }> =>
    if decide (wval e0)
    then match e0 with
         | <{ lit b }> => mret <{ ite b e1 e2 }>
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then (if v1 then e1 else e2)
                           else (if v2 then e1 else e2) }>
         | _ => None
         end
    else e0' <- step_ e0; mret <{ if e0' then e1 else e2 }>
  | <{ τ1 * τ2 }> =>
    if decide (otval τ1)
    then τ2' <- step_ τ2; mret <{ τ1 * τ2' }>
    else τ1' <- step_ τ1; mret <{ τ1' * τ2 }>
  | <{ (e1, e2) }> =>
    if decide (wval e1)
    then e2' <- step_ e2; mret <{ (e1, e2') }>
    else e1' <- step_ e1; mret <{ (e1', e2) }>
  | <{ π@b e }> =>
    if decide (wval e)
    then match e with
         | <{ (v1, v2) }> => mret <{ ite b v1 v2 }>
         | <{ ~if [b'] then v1 else v2 }> =>
          mret <{ ~if [b'] then π@b v1 else π@b v2 }>
         | _ => None
         end
    else e' <- step_ e; mret <{ π@b e' }>
  | <{ τ1 ~+ τ2 }> =>
    if decide (otval τ1)
    then τ2' <- step_ τ2; mret <{ τ1 ~+ τ2' }>
    else τ1' <- step_ τ1; mret <{ τ1' ~+ τ2 }>
  | <{ inj@b<τ> e }> => e' <- step_ e; mret <{ inj@b<τ> e' }>
  | <{ ~inj@b<τ> e }> =>
    if decide (otval τ)
    then if decide (oval e)
         then mret <{ [inj@b<τ> e] }>
         else e' <- step_ e; mret <{ ~inj@b<τ> e' }>
    else τ' <- step_ τ; mret <{ ~inj@b<τ'> e }>
  | <{ case e0 of e1 | e2 }> =>
    if decide (wval e0)
    then match e0 with
         | <{ inj@b<_> v }> => mret <{ ite b (e1^v) (e2^v) }>
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then (case v1 of e1 | e2) else (case v2 of e1 | e2) }>
         | _ => None
         end
    else e0' <- step_ e0; mret <{ case e0' of e1 | e2 }>
  | <{ ~case e0 of e1 | e2 }> =>
    if decide (wval e0)
    then match e0 with
         | <{ [inj@b<ω1 ~+ ω2> v] }> =>
           v1 <- ovalty_ ω1; v2 <- ovalty_ ω2;
           mret <{ ~if [b] then (ite b (e1^v) (e1^v1))
                           else (ite b (e2^v2) (e2^v)) }>
         | _ => None
         end
    else e0' <- step_ e0; mret <{ ~case e0' of e1 | e2 }>
  | <{ fold<X> e }> => e' <- step_ e; mret <{ fold<X> e' }>
  | <{ unfold<X> e }> =>
    if decide (wval e)
    then match e with
         | <{ fold <_> v }> => mret v
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then unfold<X> v1 else unfold<X> v2 }>
         | _ => None
         end
    else e' <- step_ e; mret <{ unfold<X> e' }>
  | <{ tape e }> =>
    if decide (woval e)
    then match e with
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ mux [b] (tape v1) (tape v2) }>
         | <{ (v1, v2) }> =>
           mret <{ (tape v1, tape v2) }>
         | <{ () }> => mret <{ () }>
         | <{ [b] }> => mret <{ [b] }>
         | <{ [inj@b<ω> v] }> => mret <{ [inj@b<ω> v] }>
         (* NOTE: Extensions *)
         | <{ i[n] }> => mret <{ i[n] }>
         | _ => None
         end
    else e' <- step_ e; mret <{ tape e' }>
  | <{ mux e0 e1 e2 }> =>
    if decide (wval e0)
    then if decide (wval e1)
         then if decide (wval e2)
              then match e0 with
                   | <{ [b] }> => mret <{ ite b e1 e2 }>
                   | _ => None
                   end
              else e2' <- step_ e2; mret <{ mux e0 e1 e2' }>
         else e1' <- step_ e1; mret <{ mux e0 e1' e2 }>
    else e0' <- step_ e0; mret <{ mux e0' e1 e2 }>
  | <{ ~if e0 then e1 else e2 }> =>
    if decide (wval e0)
    then if decide (wval e1)
         then e2' <- step_ e2; mret <{ ~if e0 then e1 else e2' }>
         else e1' <- step_ e1; mret <{ ~if e0 then e1' else e2 }>
    else e0' <- step_ e0; mret <{ ~if e0' then e1 else e2 }>
  (* NOTE: Extensions *)
  | <{ s_int e }> =>
    if decide (wval e)
    then match e with
         | <{ i(n) }> => mret <{ i[n] }>
         | <{ r_int i[n] }> => mret <{ i[n] }>
         | <{ ~if [b] then v1 else v2 }> =>
           mret <{ ~if [b] then s_int v1 else s_int v2 }>
         | _ => None
         end
    else e' <- step_ e; mret <{ s_int e' }>
  | <{ r_int e }> => e' <- step_ e; mret <{ r_int e' }>
  | <{ e1 <= e2 }> =>
    if decide (wval e1)
    then if decide (wval e2)
         then match e1, e2 with
              | <{ i(m) }>, <{ i(n) }> => mret <{ lit (leb m n) }>
              | <{ r_int i[m] }>, <{ r_int i[n] }> => mret <{ r𝔹 (i[m] ~<= i[n]) }>
              | <{ r_int i[m] }>, <{ i(n) }> => mret <{ r𝔹 (i[m] ~<= s_int i(n)) }>
              | <{ i(m) }>, <{ r_int i[n] }> => mret <{ r𝔹 (s_int i(m) ~<= i[n]) }>
              | <{ ~if [b] then v1 else v2 }>, _ =>
                  mret <{ ~if [b] then v1 <= e2 else v2 <= e2 }>
              | <{ i(m) }>, <{ ~if [b] then v1 else v2 }> =>
                mret <{ ~if [b] then i(m) <= v1 else i(m) <= v2 }>
              | _, _ => None
              end
         else e2' <- step_ e2; mret <{ e1 <= e2' }>
    else e1' <- step_ e1; mret <{ e1' <= e2 }>
  | <{ e1 ~<= e2 }> =>
    if decide (wval e1)
    then if decide (wval e2)
         then match e1, e2 with
              | <{ i[m] }>, <{ i[n] }> => mret <{ [leb m n] }>
              | _, _ => None
              end
         else e2' <- step_ e2; mret <{ e1 ~<= e2' }>
    else e1' <- step_ e1; mret <{ e1' ~<= e2 }>
  | _ => None
  end.

Fixpoint mstep_ (n : nat) (e : expr) : expr :=
  match n with
  | 0 => e
  | S n =>
      match step_ e with
      | Some e' => mstep_ n e'
      | None => e
      end
  end.


#[local]
Set Default Proof Using "Type".

Notation "e '-->!' e'" := (step Σ e e') (at level 40).
Notation "e '-->*' e'" := (rtc (step Σ) e e') (at level 40).

Lemma ovalty_sound ω : forall e,
  ovalty_ ω = Some e ->
  ovalty e ω.
Proof.
  induction ω; simpl; intros; try case_label; simplify_eq; simplify_option_eq;
    eauto using ovalty.
Qed.

Lemma step_sound e : forall e',
  step_ e = Some e' ->
  e -->! e'.
Proof.
  induction e; intros ? H; simplify_eq; simpl in H;
    try (goal_contains <{ _ _ }>; shelve);
    repeat case_decide;
    repeat
      match goal with
      | H : match ?e with _ => _ end = _ |- _ =>
          sdestruct e; simplify_eq
      end; try wval_inv; try woval_inv;
    (* Remove induction hypotheses when they are not needed to avoid unnecessary
    subgoals from [simplify_option_eq]. *)
    repeat
      match goal with
      | IH : forall _, step_ ?e = _ -> _ -->! _ |- _ =>
          assert_fails is_var e; clear IH
      end;
    simplify_option_eq;
    try solve [ eauto using step | solve_ctx ].

  eauto using step, ovalty_sound.

  Unshelve.

  repeat case_decide.
  1,3: try case_split; try wval_inv;
  repeat
    match goal with
    | IH : forall _, step_ ?e = _ -> _ -->! _ |- _ =>
        assert_fails is_var e; clear IH
    end;
  simplify_option_eq;
  try solve [ eauto using step | solve_ctx ].

  match goal with
  | H : ?e = Some ?e' |- ?T =>
      match e with
      | context [step_ ?e >>= ?k] =>
          let H' := fresh in
          assert (step_ e >>= k = Some e' -> T) as H'
              by (clear H; intros; simplify_option_eq; solve_ctx)
      end
  end.

  case_split; eauto.
  repeat case_split; eauto.
  simplify_option_eq.
  eauto using step.
Qed.

Lemma mstep_sound n : forall e e',
  mstep_ n e = e' ->
  e -->* e'.
Proof.
  induction n; simpl; intros; subst; try reflexivity.
  case_split; try reflexivity.
  eapply rtc_l; eauto using step_sound.
Qed.

End step.
