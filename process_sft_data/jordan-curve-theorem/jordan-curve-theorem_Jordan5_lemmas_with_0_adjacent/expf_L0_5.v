Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_5:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> let x_1 := cA_1 m one x in ~ expf m x_1 y -> (expf m x_1 z /\ expf m y t \/ expf m x_1 t /\ expf m y z) -> expf (L m zero x y) z t.
Proof.
intros.
rename H0 into Ez.
assert (inv_hmap (L m zero x y)).
tauto.
simpl in H0.
unfold prec_L in H0.
decompose [and] H0.
clear H0.
assert (expf (L m zero x y) y x_1).
unfold x_1 in |- *.
apply expf_L0_y_x_1.
tauto.
unfold expf in |- *.
split.
tauto.
elim H2.
clear H2.
intro.
apply MF.expo_trans with x_1.
apply MF.expo_symm.
tauto.
unfold x_1 in |- *.
assert (expf (L m zero x y) x_1 z).
unfold x_1 in |- *.
apply expf_expf_L0_3_bis.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
unfold expf in H8.
tauto.
apply MF.expo_trans with y.
apply MF.expo_symm.
tauto.
unfold expf in H6.
assert (expf (L m zero x y) y t).
apply expf_expf_L0_4_bis.
tauto.
fold x_1 in |- *.
tauto.
tauto.
unfold expf in H8.
unfold expf in H0.
tauto.
assert (expf (L m zero x y) y t).
apply expf_expf_L0_4_bis.
tauto.
fold x_1 in |- *.
tauto.
tauto.
unfold expf in H8.
tauto.
clear H2.
intros.
apply MF.expo_trans with y.
apply MF.expo_symm.
tauto.
assert (expf (L m zero x y) y z).
apply expf_expf_L0_4_bis.
tauto.
fold x_1 in |- *.
tauto.
tauto.
unfold expf in H8.
tauto.
apply MF.expo_trans with x_1.
unfold expf in H0.
tauto.
assert (expf (L m zero x y) x_1 t).
unfold x_1 in |- *.
apply expf_expf_L0_3_bis.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
unfold expf in H8.
tauto.
