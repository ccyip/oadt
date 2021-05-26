From oadt Require Import prelude.
From oadt Require Import lang_oadt.metatheories.

Module M (atom_sig : AtomSig).

Include metatheories.M atom_sig.

Module notations.
  Export syntax_notations.
  Export semantics_notations.
  Export typing_notations.
End notations.

End M.
