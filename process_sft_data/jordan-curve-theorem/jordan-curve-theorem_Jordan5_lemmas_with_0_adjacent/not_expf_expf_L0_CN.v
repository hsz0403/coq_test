Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma not_expf_expf_L0_CN: forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1:= cA_1 m one x in let x0 := cA m zero x in ~expf m x_1 y -> expf (L m zero x y) y x0.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
tauto.
rename H1 into Inv.
simpl in Inv.
unfold prec_L in Inv.
apply expf_L0_CS.
tauto.
tauto.
elim (expf_dec m (cA_1 m one x) y).
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
intros.
right.
left.
split.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H1.
unfold cF in |- *.
unfold x_1 in |- *.
unfold x0 in |- *.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
tauto.
