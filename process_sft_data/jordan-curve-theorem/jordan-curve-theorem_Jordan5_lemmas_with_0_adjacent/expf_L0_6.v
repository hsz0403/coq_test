Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_6:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> let x_1 := cA_1 m one x in ~ expf m x_1 y -> ~ expf m x_1 z -> ~ expf m y t -> expf m z t -> expf (L m zero x y) z t.
Proof.
intros.
assert (~ expf m y z).
intro.
elim H3.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_trans with z.
unfold expf in H5.
unfold expf in H4.
tauto.
unfold expf in H4.
tauto.
apply expf_expf_L0_2_bis.
tauto.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
tauto.
tauto.
