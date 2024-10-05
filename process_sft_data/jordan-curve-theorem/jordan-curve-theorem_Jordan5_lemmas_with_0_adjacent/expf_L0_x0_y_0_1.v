Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_x0_y_0_1:forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x0 := cA m zero x in let y_0_1 := cF m y in expf (L m zero x y) x0 y_0_1.
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
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H0.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y x0).
intros.
simpl in H.
unfold prec_L in H.
symmetry in a.
fold x0 in H.
tauto.
elim (eq_dart_dec (cA m zero x) x0).
intros.
unfold y_0_1 in |- *.
unfold cF in |- *.
tauto.
fold x0 in |- *.
tauto.
tauto.
simpl in H.
tauto.
simpl in H.
tauto.
