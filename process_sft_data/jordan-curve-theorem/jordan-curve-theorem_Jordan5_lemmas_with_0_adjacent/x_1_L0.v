Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma x_1_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> cA_1 m one x = cA_1 m1 one x.
Proof.
simpl in |- *.
tauto.
