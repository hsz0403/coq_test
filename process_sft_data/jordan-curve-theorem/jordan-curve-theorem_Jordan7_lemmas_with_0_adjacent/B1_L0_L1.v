Require Export Jordan6.

Lemma B1_L0_L1:forall (m:fmap)(x y x' y':dart), let m1 := L (L m one x y) zero x' y' in inv_hmap m1 -> B m1 one x = L m zero x' y'.
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
