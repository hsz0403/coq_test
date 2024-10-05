Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma y_0_1_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> cF m y = cA_1 m1 one (top m1 zero x).
Proof.
intros.
unfold cF in |- *.
unfold m1 in |- *.
rewrite <- y_0_L0.
simpl in |- *.
tauto.
fold m1 in |- *.
tauto.
