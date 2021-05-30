From oadt Require Import prelude.
From oadt Require lang_oadt.syntax.
From oadt Require lang_oadt.semantics.
From oadt Require lang_oadt.typing.
From oadt Require lang_oadt.infrastructure.
From oadt Require lang_oadt.properties.
From oadt Require lang_oadt.progress.
From oadt Require lang_oadt.preservation.
From oadt Require lang_oadt.obliviousness.

(* TODO: could we make [oadt] a namespace for symbols in [lang_oadt]? *)
Module oadt.
  Export lang_oadt.syntax.
  Export lang_oadt.semantics.
  Export lang_oadt.typing.
  Export lang_oadt.infrastructure.
  Export lang_oadt.properties.
  Export lang_oadt.progress.
  Export lang_oadt.preservation.
  Export lang_oadt.obliviousness.

  Module notations.
    Export syntax.notations.
    Export semantics.notations.
    Export typing.notations.
  End notations.

End oadt.
