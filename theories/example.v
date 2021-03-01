(** * Examples *)
Module Example.

Axiom ℕ : atom.
Axiom pred : atom.
Example nat_example := [{
  data ℕ := 𝟙 + ℕ;
  def pred : Π:ℕ, ℕ := \:ℕ => case unfold<ℕ> 0 of 1 | 0
}].

End Example.

(* TODO: explain the unconventional definition of [ectx]. *)

(* BD: Something seems off with this definition of evaluation
   contexts, as there are no inductive occurences of ectx.

   How to construct the context (v1, (v2, [ ]) ), for example?
 *)

Definition ex_ctx (e1 : expr) : expr :=
  <{ ((), ( (), e1) ) }> .

Example ex_ctx_bad : ~ ectx ex_ctx.
Proof.
  unfold ex_ctx; intro H; inversion H; subst;
    try (generalize (f_equal_help _ _ _ _ H1 (eq_refl (ELit true))); intro; discriminate);
    try (generalize (f_equal_help _ _ _ _ H0 (eq_refl (ELit true))); intro; discriminate).
Qed.

(* BD: Turn out that non-recursive contexts aren't a problem, since
   [SCTx] can be applied recursively. *)
Example ex_ctx_stuck :
  forall Σ, Σ ⊨ (ex_ctx <{if true then true else false}>) -->! <{( (), ( (), true) )}>.
Proof.
  intros; unfold ex_ctx; eauto.
  eapply SCtx with (ℇ := fun e => <{( (), e)}> );
    [repeat econstructor| ].
  eapply SCtx with (ℇ := fun e => <{( (), e)}> );
    [repeat econstructor| ].
  econstructor.
Qed.
