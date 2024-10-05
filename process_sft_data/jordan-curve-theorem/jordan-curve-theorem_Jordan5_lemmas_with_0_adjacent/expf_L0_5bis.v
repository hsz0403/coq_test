Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_5bis:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> let x_1 := cA_1 m one x in ~ expf m x_1 y -> (expf m x_1 z /\ expf m x_1 t \/ expf m y z /\ expf m y t) -> expf (L m zero x y) z t.
Proof.
intros.
elim H2.
clear H2.
intros.
decompose [and] H2.
clear H2.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with x_1.
apply MF.expo_symm.
tauto.
assert (expf (L m zero x y) x_1 z).
unfold x_1 in |- *.
apply expf_expf_L0_3_bis.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
unfold expf in H2.
tauto.
assert (expf (L m zero x y) x_1 t).
unfold x_1 in |- *.
apply expf_expf_L0_3_bis.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
unfold expf in H2.
tauto.
clear H2.
intro.
decompose [and] H2.
clear H2.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with y.
apply MF.expo_symm.
tauto.
assert (expf (L m zero x y) y z).
apply expf_expf_L0_4_bis.
tauto.
fold x_1 in |- *.
tauto.
tauto.
unfold expf in H2.
tauto.
assert (expf (L m zero x y) y t).
apply expf_expf_L0_4_bis.
tauto.
fold x_1 in |- *.
tauto.
tauto.
unfold expf in H2.
tauto.
