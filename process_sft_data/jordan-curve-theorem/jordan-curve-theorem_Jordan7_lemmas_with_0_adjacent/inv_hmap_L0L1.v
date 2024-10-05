Require Export Jordan6.

Lemma inv_hmap_L0L1:forall (m:fmap)(x y x' y':dart), let m1:= L (L m zero x y) one x' y' in let m2:= L (L m one x' y') zero x y in inv_hmap m1 -> inv_hmap m2.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
intros.
decompose [and] H.
clear H.
tauto.
