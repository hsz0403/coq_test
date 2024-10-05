Require Export Jordan6.

Lemma B0_L1_L0:forall (m:fmap)(x y x' y':dart), let m1 := L (L m zero x y) one x' y' in inv_hmap m1 -> B m1 zero x = L m one x' y'.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
elim (eq_dart_dec x x).
tauto.
tauto.
