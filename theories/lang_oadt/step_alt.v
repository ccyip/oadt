(** This file defines an alternative [step] relation. It "expands" the
evaluation context rules, resulting in a "flat" definition that is equivalent to
[step] but much convenient to use in proofs. However, it is not used at the
moment, because I have already developed enough custom tactics to deal with the
original [step] relation. *)
From oadt Require Import idt.
From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.syntax.
From oadt Require Import lang_oadt.semantics.
From oadt Require Import lang_oadt.infrastructure.

Import syntax.notations.
Import semantics.notations.

Ltac tsf_step ctor R :=
  lazymatch ctor with
  | SOIte => tsf_skip
  | SCtx => tsf_skip
  | _ => tsf_ctor_id ctor R
  end.

Ltac tsf_ectx ctor R :=
  let Σ := fresh "Σ" in
  refine (forall Σ : gctx, _ : Prop);
  lazymatch type of ctor with
  | ?P =>
      match P with
      | context [ ectx (fun e : ?T => _) ] =>
          let e' := fresh e "'" in
          refine (forall (e e' : T), R Σ e e' -> _ : Prop);
          match eval pattern ectx in P with
          | ?P _ =>
              let H := eval simpl in (P (fun ℇ => R Σ (ℇ e) (ℇ e'))) in
                exact H
          end
      end
  end.

Ltac tsf_lectx ctor R :=
  let Σ := fresh "Σ" in
  let b := fresh "b" in
  let v1 := fresh "v1" in
  let v2 := fresh "v2" in
  refine (forall (Σ : gctx) b (v1 v2 : expr), wval v1 -> wval v2 -> _ : Prop);
    lazymatch type of ctor with
    | ?P =>
        match P with
        | context [ lectx (fun e : ?T => _) ] =>
            match eval pattern lectx in P with
            | ?P _ =>
                let H := eval simpl in (P (fun ℇ => R Σ (ℇ <{ ~if [b] then v1 else v2 }>) (<{ ~if [b] then ,(ℇ v1) else ,(ℇ v2) }>))) in
                  exact H
            end
        end
  end.

MetaCoq Run (tsf_ind_gen_from
               step "step_alt"
               (ltac:(tsf_ctors step (append "A") tsf_step) ++
                ltac:(tsf_ctors ectx (append "AS") tsf_ectx) ++
                ltac:(tsf_ctors lectx (append "AS") tsf_lectx))).

Lemma step_alt_consistent Σ e e' :
  step Σ e e' <->
  step_alt Σ e e'.
Proof.
  split.
  - induction 1; try ectx_inv; eauto using step_alt.
  - induction 1; eauto using step; try solve_ctx.
Qed.
