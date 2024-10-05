Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma y_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> y = cA m1 zero x.
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x x).
tauto.
tauto.
