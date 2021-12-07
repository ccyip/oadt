From oadt Require Import idt.
From oadt.lang_oadt Require Import base syntax.
Import syntax.notations.

(** * Indistinguishability *)

(** Instead of formalizing an observe function and considering two expressions
indistinguishable if they are observed the same, we directly formalize the
indistinguishability relation as the equivalence induced by the observe
function.

All rules but the rules for boxed expressions are just congruence rules. Some
rules are not necessary if the expressions are well-typed, but we include them
anyway. *)

Module kernel.

Reserved Notation "e '≈' e'" (at level 40).

Inductive indistinguishable : expr -> expr -> Prop :=
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

End kernel.

(** Generate other congruence rules. *)
Ltac tsf_indistinguishable_congr ctor R :=
  lazymatch ctor with
  | EBoxedLit => tsf_skip
  | EBoxedInj => tsf_skip
  | _ =>
      let rec go T c c' :=
        lazymatch T with
        | forall a : ?T, ?T' =>
            lazymatch T with
            | expr =>
                let a' := fresh a "'" in
                refine (forall (a a' : T), R a a' -> _ : Prop);
                go T' constr:(c a) constr:(c' a')
            | _ =>
                refine (forall a : T, _ : Prop);
                go T' constr:(c a) constr:(c' a)
            end
        | _ => exact (R c c')
        end
      in let T := type of ctor in go T ctor ctor
    end.

MetaCoq Run (tsf_ind_gen
               (expr -> expr -> Prop)
               "indistinguishable"
               (ltac:(tsf_ctors expr (append "I" ∘ string_drop 1) tsf_indistinguishable_congr) ++
                ltac:(tsf_ctors_id kernel.indistinguishable))).

(** * Notations *)
Module notations.

Notation "e '≈' e'" := (indistinguishable e e') (at level 40).

End notations.
