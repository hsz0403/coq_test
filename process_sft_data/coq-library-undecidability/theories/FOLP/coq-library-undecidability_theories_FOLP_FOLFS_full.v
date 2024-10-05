From Undecidability Require Export FOLP.Util.FullTarski.
Definition listable X := exists L, forall x : X, In x L.
Section Finsat.
Variable Sigma : Signature.
Variable eqp : Preds.
Hypothesis Heqp : 2 = pred_ar eqp.
Definition i_eqp D (I : interp D) x y := @i_P Sigma D I eqp (cast (Vector.cons x (Vector.cons y Vector.nil)) Heqp).
Definition finsat phi := exists D (I : interp D) rho, listable D /\ (forall x y, i_eqp I x y <-> eq x y) /\ rho ⊨ phi.
End Finsat.