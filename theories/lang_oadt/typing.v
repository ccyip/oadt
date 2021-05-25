From oadt Require Import prelude.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.

(** * Typing *)

Module typing (atom_sig : AtomSig).

Module Export semantics := semantics atom_sig.
Import syntax.notations.
Import semantics.notations.

Implicit Types (x X y Y : atom) (L : aset).
Implicit Types (b : bool).

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

Inductive typing (Σ : gctx) : tctx -> expr -> expr -> Prop :=
| TFVar Γ x τ κ :
    Γ !! x = Some τ ->
    Γ ⊢ τ :: κ ->
    Γ ⊢ fvar x : τ
| TGVar Γ x τ e :
    Σ !! x = Some (DFun τ e) ->
    Γ ⊢ gvar x : τ
| TAbs Γ e τ1 τ2 κ L :
    (forall x, x ∉ L -> <[x:=τ2]>Γ ⊢ e^x : τ1^x) ->
    Γ ⊢ τ2 :: κ ->
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

with kinding (Σ : gctx) : tctx -> expr -> kind -> Prop :=
| KVarADT Γ X τ :
    Σ !! X = Some (DADT τ) ->
    Γ ⊢ gvar X :: *@P
| KUnit Γ : Γ ⊢ 𝟙 :: *@A
| KBool Γ : Γ ⊢ 𝔹 :: *@P
| KOBool Γ : Γ ⊢ ~𝔹 :: *@O
| KPi Γ τ1 τ2 κ1 κ2 L :
    (forall x, x ∉ L -> <[x:=τ1]>Γ ⊢ τ2^x :: κ2) ->
    Γ ⊢ τ1 :: κ1 ->
    Γ ⊢ (Π:τ1, τ2) :: *@M
| KApp Γ e' e τ X :
    Σ !! X = Some (DOADT τ e') ->
    Γ ⊢ e : τ ->
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
| KSub Γ τ κ κ' :
    Γ ⊢ τ :: κ' ->
    κ' ⊑ κ ->
    Γ ⊢ τ :: κ

where "Γ '⊢' e ':' τ" := (typing _ Γ e τ) and "Γ '⊢' τ '::' κ" := (kinding _ Γ τ κ)
.

Notation "Σ ; Γ '⊢' e ':' τ" := (typing Σ Γ e τ)
                                  (at level 40,
                                   Γ constr at level 0,
                                   e custom oadt at level 99,
                                   τ custom oadt at level 99).
Notation "Σ ; Γ '⊢' τ '::' κ" := (kinding Σ Γ τ κ)
                                   (at level 40,
                                    Γ constr at level 0,
                                    τ custom oadt at level 99,
                                    κ custom oadt at level 99).

(** ** Global definitions typing *)
Reserved Notation "Σ '=[' D ']=>' Σ'" (at level 40,
                                       D custom oadt_def at level 99).

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
| TFun Σ X τ e κ :
    Σ !! X = None ->
    Σ; ∅ ⊢ τ :: κ ->
    <[X:=DFun τ e]>Σ ; ∅ ⊢ e : τ ->
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
  ∅ ={ Ds }=> Σ /\ Σ; ∅ ⊢ e : τ.

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
Module notations.

Export kind_notations.

Notation "Σ '⊢' e '≡' e'" := (expr_equiv Σ e e')
                               (at level 40,
                                e custom oadt at level 99,
                                e' custom oadt at level 99).

Notation "Σ ; Γ '⊢' e ':' τ" := (typing Σ Γ e τ)
                                  (at level 40,
                                   Γ constr at level 0,
                                   e custom oadt at level 99,
                                   τ custom oadt at level 99).
Notation "Σ ; Γ '⊢' τ '::' κ" := (kinding Σ Γ τ κ)
                                   (at level 40,
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

End notations.

End typing.
