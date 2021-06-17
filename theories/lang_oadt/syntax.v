From oadt Require Import lang_oadt.base.

(** * Syntax *)

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Declare Custom Entry oadt.
Declare Custom Entry oadt_def.

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
(** Oblivious case if the label is [high], otherwise public case *)
| ECase (l : bool) (e0 : expr) (e1 : expr) (e2 : expr)
(** Types *)
| EUnitT
(** Oblivious Boolean if the label is [high], otherwise public Boolean *)
| EBool (l : bool)
| EProd (τ1 τ2 : expr)
(** Oblivious sum if the label is [high], otherwise public sum *)
| ESum (l : bool) (τ1 τ2 : expr)
(** Other expressions *)
| EApp (e1 e2 : expr)
| EUnitV
| ELit (b : bool)
| ESec (e : expr)
(** Oblivious condition (i.e. MUX) if the label is [high], otherwise public
condition *)
| EIte (l : bool) (e0 e1 e2 : expr)
| EPair (e1 e2 : expr)
| EProj (b : bool) (e : expr)
(** Oblivious injection if the label is [high], otherwise public injection *)
| EInj (l : bool) (b : bool) (τ e : expr)
| EFold (X : atom) (e : expr)
| EUnfold (X : atom) (e : expr)
(** Runtime expressions *)
| EBoxedLit (b : bool)
| EBoxedInj (b : bool) (τ e : expr)
.

(** ** Global definitions (D) *)
Variant gdef :=
| DADT (e : expr)
| DOADT (τ e : expr)
| DFun (τ e : expr)
.

(** ** Global context (Σ) *)
(** A store of global definitions. *)
Notation gctx := (amap gdef).

(** ** Programs (P) *)
Notation program := (gctx * expr).


(** ** Notations for expressions *)
Module expr_notations.

(* Adapted from _Software Foundations_. *)
Coercion ELit : bool >-> expr.
Coercion EBVar : nat >-> expr.

Notation "<{ e }>" := e (e custom oadt at level 99).

Notation "'high'" := (true) (only parsing).
Notation "'low'" := (false) (only parsing).

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
Notation "'𝔹{' l '}'" := (EBool l) (in custom oadt at level 0,
                                       l constr at level 0,
                                       format "'𝔹{' l '}'").
Notation "'𝔹'" := (EBool low) (in custom oadt at level 0).
Notation "'Bool'" := (EBool low) (in custom oadt at level 0, only parsing).
Notation "'~𝔹'" := (EBool high) (in custom oadt at level 0).
Notation "'~Bool'" := (EBool high) (in custom oadt at level 0, only parsing).
Notation "τ1 * τ2" := (EProd τ1 τ2) (in custom oadt at level 2,
                                        τ1 custom oadt,
                                        τ2 custom oadt at level 0).
Notation "τ1 '+{' l '}' τ2" := (ESum l τ1 τ2) (in custom oadt at level 3,
                                                  l constr at level 0,
                                                  left associativity,
                                                  format "τ1  '+{' l '}'  τ2").
Notation "τ1 + τ2" := (ESum low τ1 τ2) (in custom oadt at level 3,
                                           left associativity).
Notation "τ1 ~+ τ2" := (ESum high τ1 τ2) (in custom oadt at level 3,
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
Notation "'if{' l '}' e0 'then' e1 'else' e2" := (EIte l e0 e1 e2)
                                                   (in custom oadt at level 89,
                                                       l constr at level 0,
                                                       e0 custom oadt at level 99,
                                                       e1 custom oadt at level 99,
                                                       e2 custom oadt at level 99,
                                                       left associativity,
                                                       format "'if{' l '}'  e0  'then'  e1  'else'  e2").
Notation "'if' e0 'then' e1 'else' e2" := (EIte low e0 e1 e2)
                                            (in custom oadt at level 89,
                                                e0 custom oadt at level 99,
                                                e1 custom oadt at level 99,
                                                e2 custom oadt at level 99,
                                                left associativity).
Notation "'~if' e0 'then' e1 'else' e2" := (EIte high e0 e1 e2)
                                             (in custom oadt at level 89,
                                                 e0 custom oadt at level 99,
                                                 e1 custom oadt at level 99,
                                                 e2 custom oadt at level 99).
Notation "'let' e1 'in' e2" := (ELet e1 e2)
                                 (in custom oadt at level 0,
                                     e1 custom oadt at level 99,
                                     e2 custom oadt at level 99).
Notation "'inj{' l '}@' b < τ > e" := (EInj l b τ e) (in custom oadt at level 0,
                                                         l constr at level 0,
                                                         b constr at level 0,
                                                         τ custom oadt at level 0,
                                                         e custom oadt at level 0,
                                                         format "'inj{' l '}@' b < τ >  e").
Notation "'inj@' b < τ > e" := (EInj low b τ e) (in custom oadt at level 0,
                                                    b constr at level 0,
                                                    τ custom oadt at level 0,
                                                    e custom oadt at level 0,
                                                    format "inj@ b < τ >  e").
Notation "'inl' < τ > e" := (EInj low true τ e) (in custom oadt at level 0,
                                                    τ custom oadt at level 0,
                                                    e custom oadt at level 0,
                                                    format "inl < τ >  e").
Notation "'inr' < τ > e" := (EInj low false τ e) (in custom oadt at level 0,
                                                     τ custom oadt at level 0,
                                                     e custom oadt at level 0,
                                                     format "inr < τ >  e").
Notation "'~inj@' b < τ > e" := (EInj high b τ e) (in custom oadt at level 0,
                                                      b constr at level 0,
                                                      τ custom oadt at level 0,
                                                      e custom oadt at level 0,
                                                      format "~inj@ b < τ >  e").
Notation "'~inl' < τ > e" := (EInj high true τ e) (in custom oadt at level 0,
                                                      τ custom oadt at level 0,
                                                      e custom oadt at level 0,
                                                      format "~inl < τ >  e").
Notation "'~inr' < τ > e" := (EInj high false τ e) (in custom oadt at level 0,
                                                       τ custom oadt at level 0,
                                                       e custom oadt at level 0,
                                                       format "~inr < τ >  e").
(* I still want to use high and low *)
Notation "'case{' l '}' e0 'of' e1 '|' e2" :=
  (ECase l e0 e1 e2) (in custom oadt at level 89,
                         l constr at level 0,
                         e0 custom oadt at level 99,
                         e1 custom oadt at level 99,
                         e2 custom oadt at level 99,
                         left associativity,
                         format "'case{' l '}'  e0  'of'  e1  '|'  e2").
Notation "'case' e0 'of' e1 '|' e2" :=
  (ECase low e0 e1 e2) (in custom oadt at level 89,
                           e0 custom oadt at level 99,
                           e1 custom oadt at level 99,
                           e2 custom oadt at level 99,
                           left associativity).
Notation "'~case' e0 'of' e1 '|' e2" :=
  (ECase high e0 e1 e2) (in custom oadt at level 89,
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

End expr_notations.


(** ** Various Definitions *)
Section definitions.

Import expr_notations.
#[local]
Coercion EFVar : atom >-> expr.

(** ** Indistinguishability *)

(** Instead of formalizing an observe function and considering two expressions
indistinguishable if they are observed the same, we directly formalize the
indistinguishability relation as the equivalence induced by the observe
function. *)
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
| ICase l e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ case{l} e0 of e1 | e2 }> ≈ <{ case{l} e0' of e1' | e2' }>
| IUnitT : <{ 𝟙 }> ≈ <{ 𝟙 }>
| IBool l : <{ 𝔹{l} }> ≈ <{ 𝔹{l} }>
| IProd τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ τ1 * τ2 }> ≈ <{ τ1' * τ2' }>
| ISum l τ1 τ1' τ2 τ2' :
    τ1 ≈ τ1' ->
    τ2 ≈ τ2' ->
    <{ τ1 +{l} τ2 }> ≈ <{ τ1' +{l} τ2' }>
| IApp e1 e1' e2 e2' :
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ e1 e2 }> ≈ <{ e1' e2' }>
| IUnitV : <{ () }> ≈ <{ () }>
| ILit b : <{ lit b }> ≈ <{ lit b }>
| ISec e e' :
    e ≈ e' ->
    <{ s𝔹 e }> ≈ <{ s𝔹 e' }>
| IIte l e0 e0' e1 e1' e2 e2' :
    e0 ≈ e0' ->
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ if{l} e0 then e1 else e2 }> ≈ <{ if{l} e0' then e1' else e2' }>
| IPair e1 e1' e2 e2' :
    e1 ≈ e1' ->
    e2 ≈ e2' ->
    <{ (e1, e2) }> ≈ <{ (e1', e2') }>
| IProj b e e' :
    e ≈ e' ->
    <{ π@b e }> ≈ <{ π@b e' }>
| IInj l b τ τ' e e' :
    τ ≈ τ' ->
    e ≈ e' ->
    <{ inj{l}@b<τ> e }> ≈ <{ inj{l}@b<τ'> e' }>
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
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {k~>s}e0 of {S k~>s}e1 | {S k~>s}e2 }>
  (** Congruence rules *)
  | <{ τ1 * τ2 }> => <{ ({k~>s}τ1) * ({k~>s}τ2) }>
  | <{ τ1 +{l} τ2 }> => <{ ({k~>s}τ1) +{l} ({k~>s}τ2) }>
  | <{ e1 e2 }> => <{ ({k~>s}e1) ({k~>s}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({k~>s}e) }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} {k~>s}e0 then {k~>s}e1 else {k~>s}e2 }>
  | <{ (e1, e2) }> => <{ ({k~>s}e1, {k~>s}e2) }>
  | <{ π@b e }> => <{ π@b ({k~>s}e) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({k~>s}τ)> ({k~>s}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({k~>s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({k~>s}e) }>
  | _ => e
  end

where "'{' k '~>' s '}' e" := (open_ k s e) (in custom oadt).

Definition open s e := open_ 0 s e.
Notation "e ^ s" := (open s e) (in custom oadt at level 20).

(** ** Substitution (for local free variables) *)
Reserved Notation "'{' x '↦' s '}' e" (in custom oadt at level 20, x constr).

Fixpoint subst (x : atom) (s : expr) (e : expr) : expr :=
  match e with
  | <{ fvar y }> => if decide (x = y) then s else e
  (** Congruence rules *)
  | <{ Π:τ1, τ2 }> => <{ Π:{x↦s}τ1, {x↦s}τ2 }>
  | <{ \:τ => e }> => <{ \:{x↦s}τ => {x↦s}e }>
  | <{ let e1 in e2 }> => <{ let {x↦s}e1 in {x↦s}e2 }>
  | <{ case{l} e0 of e1 | e2 }> => <{ case{l} {x↦s}e0 of {x↦s}e1 | {x↦s}e2 }>
  | <{ τ1 * τ2 }> => <{ ({x↦s}τ1) * ({x↦s}τ2) }>
  | <{ τ1 +{l} τ2 }> => <{ ({x↦s}τ1) +{l} ({x↦s}τ2) }>
  | <{ e1 e2 }> => <{ ({x↦s}e1) ({x↦s}e2) }>
  | <{ s𝔹 e }> => <{ s𝔹 ({x↦s}e) }>
  | <{ if{l} e0 then e1 else e2 }> => <{ if{l} {x↦s}e0 then {x↦s}e1 else {x↦s}e2 }>
  | <{ (e1, e2) }> => <{ ({x↦s}e1, {x↦s}e2) }>
  | <{ π@b e }> => <{ π@b ({x↦s}e) }>
  | <{ inj{l}@b<τ> e }> => <{ inj{l}@b<({x↦s}τ)> ({x↦s}e) }>
  | <{ fold<X> e }> => <{ fold<X> ({x↦s}e) }>
  | <{ unfold<X> e }> => <{ unfold<X> ({x↦s}e) }>
  | _ => e
  end

where "'{' x '↦' s '}' e" := (subst x s e) (in custom oadt).

(** ** Oblivious type values (ω) *)
Inductive otval : expr -> Prop :=
| OVUnitT : otval <{ 𝟙 }>
| OVOBool : otval <{ ~𝔹 }>
| OVProd ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 * ω2 }>
| OVOSum ω1 ω2 : otval ω1 -> otval ω2 -> otval <{ ω1 ~+ ω2 }>
.

(** ** Oblivious values (v) *)
Inductive oval : expr -> Prop :=
| OVUnitV : oval <{ () }>
| OVBoxedLit b : oval <{ [b] }>
| OVPair v1 v2 : oval v1 -> oval v2 -> oval <{ (v1, v2) }>
| OVBoxedInj b ω v : otval ω -> oval v -> oval <{ [inj@b<ω> v] }>
.

(** ** Values (v) *)
Inductive val : expr -> Prop :=
| VUnitV : val <{ () }>
| VLit b : val <{ lit b }>
| VPair v1 v2 : val v1 -> val v2 -> val <{ (v1, v2) }>
| VAbs τ e : val <{ \:τ => e }>
| VInj b τ v : val v -> val <{ inj@b<τ> v }>
| VFold X v : val v -> val <{ fold<X> v }>
| VBoxedLit b : val <{ [b] }>
| VBoxedInj b ω v : otval ω -> oval v -> val <{ [inj@b<ω> v] }>
.

(** ** Local closure as expression well-formedness *)
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
(** Congruence rules *)
| LCUnitT : lc <{ 𝟙 }>
| LCBool l : lc <{ 𝔹{l} }>
| LCProd τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 * τ2 }>
| LCSum l τ1 τ2 : lc τ1 -> lc τ2 -> lc <{ τ1 +{l} τ2 }>
| LCApp e1 e2 : lc e1 -> lc e2 -> lc <{ e1 e2 }>
| LCUnitV : lc <{ () }>
| LCLit b : lc <{ lit b }>
| LCSec e : lc e -> lc <{ s𝔹 e }>
| LCIte l e0 e1 e2 : lc e0 -> lc e1 -> lc e2 -> lc <{ if{l} e0 then e1 else e2 }>
| LCPair e1 e2 : lc e1 -> lc e2 -> lc <{ (e1, e2) }>
| LCProj b e : lc e -> lc <{ π@b e }>
| LCInj l b τ e : lc τ -> lc e -> lc <{ inj{l}@b<τ> e }>
| LCFold X e : lc e -> lc <{ fold<X> e }>
| LCUnfold X e : lc e -> lc <{ unfold<X> e }>
| LCBoxedLit b : lc <{ [b] }>
(* Techincally this is not only locally closed, but more about
well-formedness. *)
| LCBoxedInj b ω v : otval ω -> oval v -> lc <{ [inj@b<ω> v] }>
.

End definitions.

(** ** Notations *)
Module notations.

Export expr_notations.

Notation "e '≈' e'" := (indistinguishable e e') (at level 40).

Notation "'{' k '~>' s '}' e" := (open_ k s e)
                                   (in custom oadt at level 20, k constr).
Notation "e ^ s" := (open s e) (in custom oadt at level 20).

Notation "'{' x '↦' s '}' e" := (subst x s e)
                                  (in custom oadt at level 20, x constr).
Notation "{ x '↦' s }" := (subst x s) (at level 20).

Notation "x # s" := (x ∉ stale s) (at level 40).

End notations.
