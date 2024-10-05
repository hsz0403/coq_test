Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_y_x_1:forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in expf (L m zero x y) y x_1.
Proof.
intros.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
simpl in H.
unfold prec_L in H.
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H0.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y y).
unfold x_1 in |- *.
tauto.
tauto.
tauto.
simpl in H.
tauto.
simpl in H.
tauto.
