From oadt Require Export prelude.
From stdpp Require Import gmap.

Export atom_instance.

#[global]
Opaque atom.

#[global]
Opaque amap.

#[global]
Opaque aset.

#[global]
Opaque is_atom.

Definition aamap := gmap (atom * atom).
Instance aamap_is_finmap : FinMapPack (atom * atom) aamap.
Proof.
  esplit.
  typeclasses eauto.
Defined.

#[global]
Opaque aamap.

#[global]
Opaque aamap_is_finmap.

Declare Custom Entry oadt.
Declare Custom Entry oadt_def.
