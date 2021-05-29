From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.semantics.

(** * Typing *)

Module M (sig : OADTSig).

Include semantics.M sig.
Import syntax_notations.
Import semantics_notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

#[local]
Open Scope type_scope.

(** ** Assumptions (Φ) *)
(** An assumption has the form [e ≡ e']. *)
Notation asm := (expr * expr).
Notation actx := (fset asm).

Definition actx_map (f : expr -> expr) (Φ : actx) : actx := set_map (prod_map f f) Φ.

(** ** Kinds (κ) *)
(** Essentially a kind is a security label. We do not need kind abstraction. *)
Variant kind :=
| KAny
| KPublic
| KObliv
| KMixed
.

(** [kind] has (semi-)lattice operators. *)

(** We define the partial order [⊑] on [kind] directly as a computable
function. Alternatively, we may define an "immediate" relation as the kernel,
and then take its reflexive-transitive closure. But [kind] is simple enough, so
let's do it in a simple way.

[κ1 ⊑ κ2] means [κ2] is stricter than or as strict as [κ1]. The relation can be
visualized as follow.

    M
   / \
  P   O
   \ /
    A
*)
Instance kind_eq : EqDecision kind.
Proof.
  unfold EqDecision, Decision.
  decide equality.
Defined.

Instance kind_join : Join kind :=
  fun κ1 κ2 =>
    match κ1, κ2 with
    | KAny, κ | κ, KAny => κ
    | KPublic, KObliv | KObliv, KPublic => KMixed
    | KMixed, _ | _, KMixed => KMixed
    | κ, _ => κ
    end.

Instance kind_le : SqSubsetEq kind :=
  fun κ1 κ2 => κ2 = (κ1 ⊔ κ2).

Instance kind_top : Top kind := KMixed.
Instance kind_bot : Bottom kind := KAny.

(** ** Typing context (Γ) *)
Notation tctx := (amap expr).

(** Notations for kinding *)
Module kind_notations.

Notation "*@A" := (KAny) (in custom oadt at level 0).
Notation "*@P" := (KPublic) (in custom oadt at level 0).
Notation "*@O" := (KObliv) (in custom oadt at level 0).
Notation "*@M" := (KMixed) (in custom oadt at level 0).
Infix "⊔" := (⊔) (in custom oadt at level 50).

End kind_notations.


Section typing.

Import kind_notations.
#[local]
Coercion EFVar : atom >-> expr.

(** ** Expression equivalence *)
(** Type equivalence is a placeholder for now. *)
Parameter expr_equiv : gctx -> actx -> expr -> expr -> Prop.

Notation "Σ ; Φ '⊢' e '≡' e'" := (expr_equiv Σ Φ e e')
                                   (at level 40,
                                    Φ constr at level 0,
                                    e custom oadt at level 99,
                                    e' custom oadt at level 99).

Notation "'{{' e1 ≡ e2 '}}' Φ " := (set_insert (e1, e2) Φ)
                                    (at level 30,
                                     e1 custom oadt at level 99,
                                     e2 custom oadt at level 99,
                                     Φ constr at level 0).

(** ** Expression typing and kinding *)
(** They are mutually defined. *)
Reserved Notation "Φ ; Γ '⊢' e ':' τ" (at level 40,
                                       Γ constr at level 0,
                                       e custom oadt at level 99,
                                       τ custom oadt at level 99).
Reserved Notation "Φ ; Γ '⊢' τ '::' κ" (at level 40,
                                        Γ constr at level 0,
                                        τ custom oadt at level 99,
                                        κ custom oadt at level 99).

Inductive typing (Σ : gctx) : actx -> tctx -> expr -> expr -> Prop :=
| TFVar Φ Γ x τ κ :
    Γ !! x = Some τ ->
    Φ; Γ ⊢ τ :: κ ->
    Φ; Γ ⊢ fvar x : τ
| TGVar Φ Γ x τ e :
    Σ !! x = Some (DFun τ e) ->
    Φ; Γ ⊢ gvar x : τ
| TAbs Φ Γ e τ1 τ2 κ L :
    (forall x, x ∉ L -> Φ; <[x:=τ2]>Γ ⊢ e^x : τ1^x) ->
    Φ; Γ ⊢ τ2 :: κ ->
    Φ; Γ ⊢ \:τ2 => e : (Π:τ2, τ1)
| TLet Φ Γ e1 e2 τ1 τ2 L :
    (forall x, x ∉ L -> Φ; <[x:=τ1]>Γ ⊢ e2^x : τ2^x) ->
    Φ; Γ ⊢ e1 : τ1 ->
    Φ; Γ ⊢ let e1 in e2 : τ2^e1
| TApp Φ Γ e1 e2 τ1 τ2 :
    Φ; Γ ⊢ e1 : (Π:τ2, τ1) ->
    Φ; Γ ⊢ e2 : τ2 ->
    Φ; Γ ⊢ e1 e2 : τ1^e2
| TUnit Φ Γ : Φ; Γ ⊢ () : 𝟙
| TLit Φ Γ b : Φ; Γ ⊢ lit b : 𝔹
| TSec Φ Γ e :
    Φ; Γ ⊢ e : 𝔹 ->
    Φ; Γ ⊢ s𝔹 e : ~𝔹
(* Collect the path conditions on discriminee *)
| TIte Φ Γ e0 e1 e2 τ κ :
    Φ; Γ ⊢ e0 : 𝔹 ->
    {{e0 ≡ lit true}}Φ; Γ ⊢ e1 : τ ->
    {{e0 ≡ lit false}}Φ; Γ ⊢ e2 : τ ->
    Φ; Γ ⊢ τ :: κ ->
    Φ; Γ ⊢ if e0 then e1 else e2 : τ
| TMux Φ Γ e0 e1 e2 τ :
    Φ; Γ ⊢ e0 : ~𝔹 ->
    Φ; Γ ⊢ e1 : τ ->
    Φ; Γ ⊢ e2 : τ ->
    Φ; Γ ⊢ τ :: *@O ->
    Φ; Γ ⊢ ~if e0 then e1 else e2 : τ
| TInj Φ Γ l b e τ1 τ2 :
    Φ; Γ ⊢ e : ite b τ1 τ2 ->
    Φ; Γ ⊢ τ1 +{l} τ2 :: ite l *@O *@P ->
    Φ; Γ ⊢ inj{l}@b<τ1 +{l} τ2> e : τ1 +{l} τ2
(* Collect the path conditions on discriminee *)
| TCase Φ Γ e0 e1 e2 τ1 τ2 τ κ L1 L2 :
    (forall x, x ∉ L1 -> {{e0 ≡ inl<τ1 + τ2> x}}Φ; <[x:=τ1]>Γ ⊢ e1^x : τ) ->
    (forall x, x ∉ L2 -> {{e0 ≡ inr<τ1 + τ2> x}}Φ; <[x:=τ2]>Γ ⊢ e2^x : τ) ->
    Φ; Γ ⊢ e0 : τ1 + τ2 ->
    Φ; Γ ⊢ τ :: κ ->
    Φ; Γ ⊢ case e0 of e1 | e2 : τ
| TOCase Φ Γ e0 e1 e2 τ1 τ2 τ L1 L2 :
    (forall x, x ∉ L1 -> Φ; <[x:=τ1]>Γ ⊢ e1^x : τ) ->
    (forall x, x ∉ L2 -> Φ; <[x:=τ2]>Γ ⊢ e2^x : τ) ->
    Φ; Γ ⊢ e0 : τ1 ~+ τ2 ->
    Φ; Γ ⊢ τ :: *@O ->
    Φ; Γ ⊢ ~case e0 of e1 | e2 : τ
| TPair Φ Γ e1 e2 τ1 τ2 :
    Φ; Γ ⊢ e1 : τ1 ->
    Φ; Γ ⊢ e2 : τ2 ->
    Φ; Γ ⊢ (e1, e2) : τ1 * τ2
| TProj Φ Γ b e τ1 τ2 :
    Φ; Γ ⊢ e : τ1 * τ2 ->
    Φ; Γ ⊢ π@b e : ite b τ1 τ2
| TFold Φ Γ X e τ :
    Σ !! X = Some (DADT τ) ->
    Φ; Γ ⊢ e : τ ->
    Φ; Γ ⊢ fold<X> e : gvar X
| TUnfold Φ Γ X e τ :
    Σ !! X = Some (DADT τ) ->
    Φ; Γ ⊢ e : gvar X ->
    Φ; Γ ⊢ unfold<X> e : τ
(** Typing for runtime expressions is for metatheories. These expressions do not
appear in source programs. Plus, it is not possible to type them at runtime
since they are "encrypted" values. *)
| TBoxedLit Φ Γ b : Φ; Γ ⊢ [b] : ~𝔹
| TBoxedInj Φ Γ b v ω :
    oval <{ [inj@b<ω> v] }> ω ->
    Φ; Γ ⊢ [inj@b<ω> v] : ω
(** Type conversion *)
| TConv Φ Γ e τ τ' κ :
    Φ; Γ ⊢ e : τ' ->
    Φ; Γ ⊢ τ :: κ ->
    Σ; Φ ⊢ τ' ≡ τ ->
    Φ; Γ ⊢ e : τ

with kinding (Σ : gctx) : actx -> tctx -> expr -> kind -> Prop :=
| KVarADT Φ Γ X τ :
    Σ !! X = Some (DADT τ) ->
    Φ; Γ ⊢ gvar X :: *@P
| KUnit Φ Γ : Φ; Γ ⊢ 𝟙 :: *@A
| KBool Φ Γ l : Φ; Γ ⊢ 𝔹{l} :: ite l *@O *@P
| KPi Φ Γ τ1 τ2 κ1 κ2 L :
    (forall x, x ∉ L -> Φ; <[x:=τ1]>Γ ⊢ τ2^x :: κ2) ->
    Φ; Γ ⊢ τ1 :: κ1 ->
    Φ; Γ ⊢ (Π:τ1, τ2) :: *@M
| KApp Φ Γ e' e τ X :
    Σ !! X = Some (DOADT τ e') ->
    Φ; Γ ⊢ e : τ ->
    Φ; Γ ⊢ (gvar X) e :: *@O
| KProd Φ Γ τ1 τ2 κ :
    Φ; Γ ⊢ τ1 :: κ ->
    Φ; Γ ⊢ τ2 :: κ ->
    Φ; Γ ⊢ τ1 * τ2 :: κ
| KSum Φ Γ τ1 τ2 κ :
    Φ; Γ ⊢ τ1 :: κ ->
    Φ; Γ ⊢ τ2 :: κ ->
    Φ; Γ ⊢ τ1 + τ2 :: (κ ⊔ *@P)
| KOSum Φ Γ τ1 τ2 :
    Φ; Γ ⊢ τ1 :: *@O ->
    Φ; Γ ⊢ τ2 :: *@O ->
    Φ; Γ ⊢ τ1 ~+ τ2 :: *@O
| KIte Φ Γ e0 τ1 τ2 :
    Φ; Γ ⊢ e0 : 𝔹 ->
    Φ; Γ ⊢ τ1 :: *@O ->
    Φ; Γ ⊢ τ2 :: *@O ->
    Φ; Γ ⊢ if e0 then τ1 else τ2 :: *@O
| KCase Φ Γ e0 τ1 τ2 τ1' τ2' L1 L2 :
    (forall x, x ∉ L1 -> Φ; <[x:=τ1']>Γ ⊢ τ1^x :: *@O) ->
    (forall x, x ∉ L2 -> Φ; <[x:=τ2']>Γ ⊢ τ2^x :: *@O) ->
    Φ; Γ ⊢ e0 : τ1' + τ2' ->
    Φ; Γ ⊢ case e0 of τ1 | τ2 :: *@O
| KLet Φ Γ e τ τ' L :
    (forall x, x ∉ L -> Φ; <[x:=τ']>Γ ⊢ τ^x :: *@O) ->
    Φ; Γ ⊢ e : τ' ->
    Φ; Γ ⊢ let e in τ :: *@O
| KSub Φ Γ τ κ κ' :
    Φ; Γ ⊢ τ :: κ' ->
    κ' ⊑ κ ->
    Φ; Γ ⊢ τ :: κ

where "Φ ; Γ '⊢' e ':' τ" := (typing _ Φ Γ e τ) and
      "Φ ; Γ '⊢' τ '::' κ" := (kinding _ Φ Γ τ κ)
.

Notation "Σ ; Φ ; Γ '⊢' e ':' τ" := (typing Σ Φ Γ e τ)
                                      (at level 40,
                                       Φ constr at level 0,
                                       Γ constr at level 0,
                                       e custom oadt at level 99,
                                       τ custom oadt at level 99).
Notation "Σ ; Φ ; Γ '⊢' τ '::' κ" := (kinding Σ Φ Γ τ κ)
                                       (at level 40,
                                        Φ constr at level 0,
                                        Γ constr at level 0,
                                        τ custom oadt at level 99,
                                        κ custom oadt at level 99).

(** ** Global definitions typing *)
Reserved Notation "Σ '=[' D ']=>' Σ'" (at level 40,
                                       D custom oadt_def at level 99).

Inductive gdef_typing : gctx -> (atom * gdef) -> gctx -> Prop :=
| TADT Σ X τ :
    Σ !! X = None ->
    <[X:=DADT τ]>Σ; ∅; ∅ ⊢ τ :: *@P ->
    Σ =[ data X := τ ]=> <[X:=DADT τ]>Σ
| TOADT Σ X τ e L :
    Σ !! X = None ->
    Σ; ∅; ∅ ⊢ τ :: *@P ->
    (forall x, x ∉ L -> <[X:=DOADT τ e]>Σ; ∅; ({[x:=τ]}) ⊢ e^x :: *@O) ->
    Σ =[ obliv X (:τ) := e ]=> <[X:=DOADT τ e]>Σ
| TFun Σ X τ e κ :
    Σ !! X = None ->
    Σ; ∅; ∅ ⊢ τ :: κ ->
    <[X:=DFun τ e]>Σ; ∅; ∅ ⊢ e : τ ->
    Σ =[ def X : τ := e ]=> <[X:=DFun τ e]>Σ

where "Σ '=[' D ']=>' Σ'" := (gdef_typing Σ D Σ')
.

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

(** ** Program typing *)
Definition program_typing (Ds : gdefs) (e : expr) (Σ : gctx) (τ : expr) :=
  ∅ ={ Ds }=> Σ /\ Σ; ∅; ∅ ⊢ e : τ.

End typing.

(** Better induction principle. *)
Scheme typing_kinding_ind := Minimality for typing Sort Prop
  with kinding_typing_ind := Minimality for kinding Sort Prop.
Combined Scheme typing_kinding_mutind
         from typing_kinding_ind, kinding_typing_ind.

(** ** Hints *)
Hint Constructors typing : typing.
Hint Constructors kinding : kinding.
Hint Constructors gdef_typing : gdef_typing.
Hint Constructors gdefs_typing : gdefs_typing.


(** ** Notations *)
(* Unfortunately I have to copy-paste all notations here again. *)
Module typing_notations.

Export kind_notations.

Notation "Σ ; Φ '⊢' e '≡' e'" := (expr_equiv Σ Φ e e')
                                   (at level 40,
                                    Φ constr at level 0,
                                    e custom oadt at level 99,
                                    e' custom oadt at level 99).

Notation "'{{' e1 ≡ e2 '}}' Φ " := (set_insert (e1, e2) Φ)
                                    (at level 30,
                                     e1 custom oadt at level 99,
                                     e2 custom oadt at level 99,
                                     Φ constr at level 0).

Notation "Σ ; Φ ; Γ '⊢' e ':' τ" := (typing Σ Φ Γ e τ)
                                      (at level 40,
                                       Φ constr at level 0,
                                       Γ constr at level 0,
                                       e custom oadt at level 99,
                                       τ custom oadt at level 99).
Notation "Σ ; Φ ; Γ '⊢' τ '::' κ" := (kinding Σ Φ Γ τ κ)
                                       (at level 40,
                                        Φ constr at level 0,
                                        Γ constr at level 0,
                                        τ custom oadt at level 99,
                                        κ custom oadt at level 99).

Notation "Σ '=[' D ']=>' Σ'" := (gdef_typing Σ D Σ')
                                  (at level 40,
                                   D custom oadt_def at level 99).
Notation "Σ '={' Ds '}=>' Σ'" := (gdefs_typing Σ Ds Σ')
                                   (at level 40,
                                    Ds constr at level 99).

(* Notation "Ds ; e '▷' Σ ; τ" := (program_typing Ds e Σ τ) *)
(*                                  (at level 40, *)
(*                                   e custom oadt at level 99, *)
(*                                   Σ constr at level 0, *)
(*                                   τ custom oadt at level 99). *)

End typing_notations.

End M.
