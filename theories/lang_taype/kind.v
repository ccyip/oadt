From taype.lang_taype Require Import base.

(** * Definitions *)

(** ** Kinds (κ) *)
(** Essentially a kind is a security label. We do not need kind abstraction. *)
Variant kind :=
| KAny
| KPublic
| KObliv
| KMixed
.

(** * Properties *)

(** [kind] has (semi-)lattice operators.

We define the partial order [⊑] on [kind] directly as a computable function.
Alternatively, we may define an "immediate" relation as the kernel, and then
take its reflexive-transitive closure. But [kind] is simple enough, so let's do
it in a simple way.

[κ1 ⊑ κ2] means [κ2] is stricter than or as strict as [κ1]. The relation can be
visualized as follow.

<<
    M
   / \
  P   O
   \ /
    A
>>
*)
#[global]
Instance kind_eq : EqDecision kind.
Proof.
  solve_decision.
Defined.

#[global]
Instance kind_join : Join kind :=
  fun κ1 κ2 =>
    match κ1, κ2 with
    | KAny, κ | κ, KAny => κ
    | KPublic, KObliv | KObliv, KPublic => KMixed
    | KMixed, _ | _, KMixed => KMixed
    | κ, _ => κ
    end.

#[global]
Instance kind_le : SqSubsetEq kind :=
  fun κ1 κ2 => κ2 = (κ1 ⊔ κ2).

#[global]
Instance kind_top : Top kind := KMixed.
#[global]
Instance kind_bot : Bottom kind := KAny.

(** [kind] forms a [SemiLattice].  *)
#[global]
Instance kind_semilattice : SemiLattice kind.
Proof.
  split; try reflexivity; repeat intros []; auto.
Qed.

(** * Notations *)
Module notations.

Notation "*@A" := (KAny) (in custom taype at level 0).
Notation "*@P" := (KPublic) (in custom taype at level 0).
Notation "*@O" := (KObliv) (in custom taype at level 0).
Notation "*@M" := (KMixed) (in custom taype at level 0).
Infix "⊔" := (⊔) (in custom taype at level 50).

End notations.
