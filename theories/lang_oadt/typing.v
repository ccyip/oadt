From oadt.lang_oadt Require Import base syntax semantics.
From oadt.lang_oadt Require Export kind.
Import syntax.notations semantics.notations kind.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

(** * Definitions *)

(** ** Typing context (Γ) *)
Notation tctx := (amap lexpr).

Section typing.

#[local]
Coercion EFVar : atom >-> expr.

Section fix_gctx.

Context (Σ : gctx).

(** ** Parallel reduction *)
Reserved Notation "e '⇛' e'" (at level 40).

Inductive pared : expr -> expr -> Prop :=
| RApp l τ e1 e2 e1' e2' L :
    e1 ⇛ e1' ->
    (forall x, x ∉ L -> <{ e2^x }> ⇛ <{ e2'^x }>) ->
    lc τ ->
    <{ (\:{l}τ => e2) e1 }> ⇛ <{ e2'^e1' }>
| RTApp X τ' τ e e' :
    Σ !! X = Some (DOADT τ' τ) ->
    e ⇛ e' ->
    <{ X@e }> ⇛ <{ τ^e' }>
| RLet e1 e2 e1' e2' L :
    e1 ⇛ e1' ->
    (forall x, x ∉ L -> <{ e2^x }> ⇛ <{ e2'^x }>) ->
    <{ let e1 in e2 }> ⇛ <{ e2'^e1' }>
| RFun x T e :
    Σ !! x = Some (DFun T e) ->
    <{ gvar x }> ⇛ <{ e }>
| RProj l b e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ π{l}@b (e1, e2){l} }> ⇛ <{ ite b e1' e2' }>
| RFold X X' e e' :
    e ⇛ e' ->
    <{ unfold<X> (fold<X'> e) }> ⇛ e'
| RIte b e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ if b then e1 else e2 }> ⇛ <{ ite b e1' e2' }>
| RCase b τ e0 e1 e2 e0' e1' e2' L1 L2 :
    e0 ⇛ e0' ->
    (forall x, x ∉ L1 -> <{ e1^x }> ⇛ <{ e1'^x }>) ->
    (forall x, x ∉ L2 -> <{ e2^x }> ⇛ <{ e2'^x }>) ->
    lc τ ->
    <{ case inj@b<τ> e0 of e1 | e2 }> ⇛ <{ ite b (e1'^e0') (e2'^e0') }>
(* The rules for oblivous constructs are solely for proof convenience. They are
not needed because they are not involved in type-level computation. *)
| RMux b e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ mux [b] e1 e2 }> ⇛ <{ ite b e1' e2' }>
(* This rule is needed for confluence. *)
| ROIte b e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ ~if [b] then e1 else e2 }> ⇛ <{ ite b e1' e2' }>
| ROCase b ω1 ω2 v v1 v2 e1 e2 e1' e2' L1 L2 :
    oval v ->
    ovalty v1 ω1 -> ovalty v2 ω2 ->
    (forall x, x ∉ L1 -> <{ e1^x }> ⇛ <{ e1'^x }>) ->
    (forall x, x ∉ L2 -> <{ e2^x }> ⇛ <{ e2'^x }>) ->
    <{ ~case [inj@b<ω1 ~+ ω2> v] of e1 | e2 }> ⇛
      <{ ~if [b] then (ite b (e1'^v) (e1'^v1)) else (ite b (e2'^v2) (e2'^v)) }>
| RSec b :
    <{ s𝔹 b }> ⇛ <{ [b] }>
| ROInj b ω v :
    otval ω -> oval v ->
    <{ ~inj@b<ω> v }> ⇛ <{ [inj@b<ω> v] }>
(* Unfortunately I have to spell out all the cases corresponding to [SOIte] for
proof convenience. *)
| ROIteApp b e1 e2 e e1' e2' e' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    e ⇛ e' ->
    <{ (~if [b] then e1 else e2) e }> ⇛ <{ ~if [b] then e1' e' else e2' e' }>
| ROIteSec b e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ s𝔹 (~if [b] then e1 else e2) }> ⇛ <{ ~if [b] then s𝔹 e1' else s𝔹 e2' }>
| ROIteIte b e1 e2 e3 e4 e1' e2' e3' e4' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    e3 ⇛ e3' ->
    e4 ⇛ e4' ->
    <{ if (~if [b] then e1 else e2) then e3 else e4 }> ⇛
      <{ ~if [b] then (if e1' then e3' else e4') else (if e2' then e3' else e4') }>
| ROIteProj b b' e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ π@b' (~if [b] then e1 else e2) }> ⇛
      <{ ~if [b] then π@b' e1' else π@b' e2' }>
| ROIteCase b e1 e2 e3 e4 e1' e2' e3' e4' L1 L2 :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    (forall x, x ∉ L1 -> <{ e3^x }> ⇛ <{ e3'^x }>) ->
    (forall x, x ∉ L2 -> <{ e4^x }> ⇛ <{ e4'^x }>) ->
    <{ case (~if [b] then e1 else e2) of e3 | e4 }> ⇛
      <{ ~if [b] then (case e1' of e3' | e4') else (case e2' of e3' | e4') }>
| ROIteUnfold X b e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ unfold<X> (~if [b] then e1 else e2) }> ⇛
      <{ ~if [b] then unfold<X> e1' else unfold<X> e2' }>
| RTapeOIte b e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ tape (~if [b] then e1 else e2) }> ⇛ <{ mux [b] (tape e1') (tape e2') }>
| RTapeOVal v :
    oval v ->
    <{ tape v }> ⇛ v
(* Congruence rules *)
| RCgrPi l τ1 τ2 τ1' τ2' L :
    τ1 ⇛ τ1' ->
    (forall x, x ∉ L -> <{ τ2^x }> ⇛ <{ τ2'^x }>) ->
    <{ Π:{l}τ1, τ2 }> ⇛ <{ Π:{l}τ1', τ2' }>
| RCgrAbs l τ e τ' e' L :
    τ ⇛ τ' ->
    (forall x, x ∉ L -> <{ e^x }> ⇛ <{ e'^x }>) ->
    <{ \:{l}τ => e }> ⇛ <{ \:{l}τ' => e' }>
| RCgrApp e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ e1 e2 }> ⇛ <{ e1' e2' }>
| RCgrTApp X e e' :
    e ⇛ e' ->
    <{ X@e }> ⇛ <{ X@e' }>
| RCgrLet e1 e2 e1' e2' L :
    e1 ⇛ e1' ->
    (forall x, x ∉ L -> <{ e2^x }> ⇛ <{ e2'^x }>) ->
    <{ let e1 in e2 }> ⇛ <{ let e1' in e2' }>
| RCgrSec e e' :
    e ⇛ e' ->
    <{ s𝔹 e }> ⇛ <{ s𝔹 e' }>
| RCgrIte l e0 e1 e2 e0' e1' e2' :
    e0 ⇛ e0' ->
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ if{l} e0 then e1 else e2 }> ⇛ <{ if{l} e0' then e1' else e2' }>
| RCgrProd l τ1 τ2 τ1' τ2' :
    τ1 ⇛ τ1' ->
    τ2 ⇛ τ2' ->
    <{ τ1 *{l} τ2 }> ⇛ <{ τ1' *{l} τ2' }>
| RCgrPair l e1 e2 e1' e2' :
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ (e1, e2){l} }> ⇛ <{ (e1', e2'){l} }>
| RCgrProj l b e e' :
    e ⇛ e' ->
    <{ π{l}@b e }> ⇛ <{ π{l}@b e' }>
| RCgrSum l τ1 τ2 τ1' τ2' :
    τ1 ⇛ τ1' ->
    τ2 ⇛ τ2' ->
    <{ τ1 +{l} τ2 }> ⇛ <{ τ1' +{l} τ2' }>
| RCgrInj l b τ e τ' e' :
    e ⇛ e' ->
    τ ⇛ τ' ->
    <{ inj{l}@b<τ> e }> ⇛ <{ inj{l}@b<τ'> e' }>
| RCgrCase l e0 e1 e2 e0' e1' e2' L1 L2 :
    e0 ⇛ e0' ->
    (forall x, x ∉ L1 -> <{ e1^x }> ⇛ <{ e1'^x }>) ->
    (forall x, x ∉ L2 -> <{ e2^x }> ⇛ <{ e2'^x }>) ->
    <{ case{l} e0 of e1 | e2 }> ⇛ <{ case{l} e0' of e1' | e2' }>
| RCgrFold X e e' :
    e ⇛ e' ->
    <{ fold<X> e }> ⇛ <{ fold<X> e' }>
| RCgrUnfold X e e' :
    e ⇛ e' ->
    <{ unfold<X> e }> ⇛ <{ unfold<X> e' }>
| RCgrMux e0 e1 e2 e0' e1' e2' :
    e0 ⇛ e0' ->
    e1 ⇛ e1' ->
    e2 ⇛ e2' ->
    <{ mux e0 e1 e2 }> ⇛ <{ mux e0' e1' e2' }>
| RCgrTape e e' :
    e ⇛ e' ->
    <{ tape e }> ⇛ <{ tape e' }>
(* Reflexive rule *)
| RRefl e :
    lc e ->
    e ⇛ e

where "e1 '⇛' e2" := (pared e1 e2)
.

Notation "e '⇛*' e'" := (rtc pared e e') (at level 40).

(** ** Expression equivalence *)
(** We directly define equivalence in terms of parallel reduction. *)

(** This definition is the same as saying two expressions multi-reduce to the
same expression (i.e. [pared_equiv_join] below), but easier for induction in
most cases. *)
Inductive pared_equiv : expr -> expr -> Prop :=
| QRRefl e : e ≡ e
| QRRedL e1 e1' e2 :
    e1 ⇛ e1' ->
    e1' ≡ e2 ->
    e1 ≡ e2
| QRRedR e1 e2 e2' :
    e2 ⇛ e2' ->
    e1 ≡ e2' ->
    e1 ≡ e2

where "e1 ≡ e2" := (pared_equiv e1 e2)
.

(** This is equivalent to [pared_equiv]. *)
Definition pared_equiv_join (e1 e2 : expr) : Prop :=
  exists e, e1 ⇛* e /\ e2 ⇛* e.

(** ** Typing and kinding *)
(** They are mutually defined. *)
Reserved Notation "Γ '⊢' e ':{' l '}' τ" (at level 40,
                                          e custom oadt at level 99,
                                          l constr at level 99,
                                          τ custom oadt at level 99).
Reserved Notation "Γ '⊢' τ '::' κ" (at level 40,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

Inductive typing : tctx -> expr -> llabel -> expr -> Prop :=
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
| TLet Γ l1 l2 e1 e2 τ1 τ2 L :
    Γ ⊢ e1 :{l1} τ1 ->
    (forall x, x ∉ L -> <[x:=(l1, τ1)]>Γ ⊢ e2^x :{l2} τ2^x) ->
    Γ ⊢ let e1 in e2 :{l2} τ2^e1
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
| TOPair Γ e1 e2 τ1 τ2 :
    Γ ⊢ e1 :{⊥} τ1 ->
    Γ ⊢ e2 :{⊥} τ2 ->
    Γ ⊢ τ1 :: *@O ->
    Γ ⊢ τ2 :: *@O ->
    Γ ⊢ ~(e1, e2) :{⊥} τ1 ~* τ2
| TProj Γ l b e τ1 τ2 :
    Γ ⊢ e :{l} τ1 * τ2 ->
    Γ ⊢ π@b e :{l} ite b τ1 τ2
| TOProj Γ b e τ1 τ2 :
    Γ ⊢ e :{⊥} τ1 ~* τ2 ->
    Γ ⊢ ~π@b e :{⊥} ite b τ1 τ2
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
(* Typing for runtime expressions is for metatheories. These expressions do not
appear in source programs. Plus, it is not possible to type them at runtime
since they are "encrypted" values. *)
| TBoxedLit Γ b : Γ ⊢ [b] :{⊥} ~𝔹
| TBoxedInj Γ b v ω :
    ovalty <{ [inj@b<ω> v] }> ω ->
    Γ ⊢ [inj@b<ω> v] :{⊥} ω
(* Type conversion *)
| TConv Γ l l' e τ τ' κ :
    Γ ⊢ e :{l'} τ' ->
    τ' ≡ τ ->
    Γ ⊢ τ :: κ ->
    l' ⊑ l ->
    Γ ⊢ e :{l} τ

with kinding : tctx -> expr -> kind -> Prop :=
| KGVar Γ X τ :
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
    Γ ⊢ X@e :: *@O
| KProd Γ τ1 τ2 κ :
    Γ ⊢ τ1 :: κ ->
    Γ ⊢ τ2 :: κ ->
    Γ ⊢ τ1 * τ2 :: (κ ⊔ *@P)
| KOProd Γ τ1 τ2 :
    Γ ⊢ τ1 :: *@O ->
    Γ ⊢ τ2 :: *@O ->
    Γ ⊢ τ1 ~* τ2 :: *@O
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
                                           Γ constr at next level,
                                           e custom oadt at level 99,
                                           τ custom oadt at level 99,
                                           format "Σ ;  Γ  '⊢'  e  ':{' l '}'  τ").
Notation "Σ ; Γ '⊢' τ '::' κ" := (kinding Σ Γ τ κ)
                                   (at level 40,
                                    Γ constr at next level,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

(** ** Global definitions typing *)
Reserved Notation "Σ '⊢₁' D" (at level 40).

Inductive gdef_typing : gctx -> gdef -> Prop :=
| DTADT Σ τ :
    Σ; ∅ ⊢ τ :: *@P ->
    Σ ⊢₁ (DADT τ)
| DTOADT Σ τ e L :
    Σ; ∅ ⊢ τ :: *@P ->
    (forall x, x ∉ L -> Σ; ({[x:=(⊥, τ)]}) ⊢ e^x :: *@O) ->
    Σ ⊢₁ (DOADT τ e)
| DTFun Σ l τ e κ :
    Σ; ∅ ⊢ τ :: κ ->
    Σ; ∅ ⊢ e :{l} τ ->
    Σ ⊢₁ (DFun (l, τ) e)

where "Σ '⊢₁' D" := (gdef_typing Σ D)
.

Definition gctx_typing (Σ : gctx) : Prop :=
  map_Forall (fun _ D => Σ ⊢₁ D) Σ.

(** ** Program typing *)
(** The top level expression should not contain potential leaks. *)
Definition program_typing (Σ : gctx) (e : expr) (τ : expr) :=
  gctx_typing Σ /\ Σ; ∅ ⊢ e :{⊥} τ.

(** ** Well-formedness of global context *)
(** Equivalent to [gctx_typing]. Essentially saying all definitions in [Σ] are
well-typed. *)
(* TODO: I should use a weaker assumption in some proofs, such as all global
definitions are locally closed. *)
Definition gctx_wf (Σ : gctx) :=
  map_Forall (fun _ D =>
                match D with
                | DADT τ =>
                  Σ; ∅ ⊢ τ :: *@P
                | DOADT τ e =>
                  Σ; ∅ ⊢ τ :: *@P /\
                  exists L, forall x, x ∉ L -> Σ; ({[x:=(⊥, τ)]}) ⊢ e^x :: *@O
                | DFun (l, τ) e =>
                  Σ; ∅ ⊢ e :{l} τ /\
                  exists κ, Σ; ∅ ⊢ τ :: κ
                end) Σ.

End typing.

(** * Notations *)
(* Unfortunately I have to copy-paste all notations here again. *)
Module notations.

Export kind.notations.

Notation "Σ '⊢' e '⇛' e'" := (pared Σ e e')
                               (at level 40,
                                 e custom oadt at level 99,
                                 e' custom oadt at level 99).
Notation "Σ '⊢' e '⇛*' e'" := (rtc (pared Σ) e e')
                                (at level 40,
                                  e custom oadt at level 99,
                                  e' custom oadt at level 99).
Notation "Σ '⊢' e '≡' e'" := (pared_equiv Σ e e')
                               (at level 40,
                                e custom oadt at level 99,
                                e' custom oadt at level 99).
Notation "Σ ; Γ '⊢' e ':{' l '}' τ" := (typing Σ Γ e l τ)
                                         (at level 40,
                                           Γ constr at next level,
                                           e custom oadt at level 99,
                                           τ custom oadt at level 99,
                                           format "Σ ;  Γ  '⊢'  e  ':{' l '}'  τ").
Notation "Σ ; Γ '⊢' e ':' τ" := (typing Σ Γ e _ τ)
                                         (at level 40,
                                           Γ constr at next level,
                                           e custom oadt at level 99,
                                           τ custom oadt at level 99,
                                           only parsing).
Notation "Σ ; Γ '⊢' τ '::' κ" := (kinding Σ Γ τ κ)
                                   (at level 40,
                                    Γ constr at next level,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

Notation "Σ '⊢₁' D" := (gdef_typing Σ D) (at level 40).

Notation "Σ ; e '▷' τ" := (program_typing Σ e τ)
                            (at level 40,
                              e at next level).

Notation "e '⇛' e'" := (pared _ e e') (at level 40).
Notation "e '⇛*' e'" := (rtc (pared _) e e') (at level 40).

Notation "Γ '⊢' e ':{' l '}' τ" := (typing _ Γ e l τ)
                                     (at level 40,
                                       e custom oadt at level 99,
                                       l constr at level 99,
                                       τ custom oadt at level 99,
                                       format "Γ  '⊢'  e  ':{' l '}'  τ").
Notation "Γ '⊢' e ':' τ" := (typing _ Γ e _ τ)
                              (at level 40,
                                e custom oadt at level 99,
                                τ custom oadt at level 99,
                                only parsing).
Notation "Γ '⊢' τ '::' κ" := (kinding _ Γ τ κ)
                               (at level 40,
                                 τ custom oadt at level 99,
                                 κ custom oadt at level 99).
End notations.
