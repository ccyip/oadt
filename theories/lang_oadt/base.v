From oadt Require Export prelude.

Parameter atom : Type.
Parameter amap : Type -> Type.
Parameter aset : Type.
Parameter is_atom : Atom atom amap aset.

#[export]
Hint Resolve is_atom : typeclass_instances.

Parameter fset : Type -> Type.
Parameter is_polyfinset : PolyFinSet fset.

#[export]
Hint Resolve is_polyfinset : typeclass_instances.
