From oadt Require Export prelude.

Module Type OADTSig.

  Context `(is_atom : Atom atom amap aset).

  #[export]
  Hint Resolve is_atom : typeclass_instances.

  Context `(is_polyfinset : PolyFinSet fset).

  #[export]
  Hint Resolve is_polyfinset : typeclass_instances.

End OADTSig.

Declare Custom Entry oadt.
Declare Custom Entry oadt_def.
