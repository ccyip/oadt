From oadt Require Import lang_oadt.base.
From oadt Require Import lang_oadt.metatheories.

Module M (sig : OADTSig).

Include metatheories.M sig.

Module notations.
  Export syntax_notations.
  Export semantics_notations.
  Export typing_notations.
End notations.

End M.
