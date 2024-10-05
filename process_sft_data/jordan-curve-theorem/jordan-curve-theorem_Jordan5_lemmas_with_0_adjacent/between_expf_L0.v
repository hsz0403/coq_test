Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma between_expf_L0:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in let y_0_1 := cF m y in let x0 := cA m zero x in (betweenf m x_1 z y /\ betweenf m x_1 t y \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0) -> expf (L m zero x y) z t.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
tauto.
rename H1 into H'.
simpl in H'.
unfold prec_L in H'.
decompose [and] H'.
assert (exd m (cA_1 m one x)).
generalize (exd_cA_1 m one x).
tauto.
assert (exd m (cF m y)).
unfold cF in |- *.
generalize (exd_cA_1 m one (cA_1 m zero y)).
generalize (exd_cA_1 m zero y).
tauto.
intuition.
generalize H0 H16.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
intros.
fold x_1 in H6.
generalize (H14 H9 H6).
clear H14.
intro.
elim H14.
intros i Hi.
elim Hi.
intros j Hj.
clear Hi.
clear H14.
elim H17.
intros i' Hi.
clear H17.
elim Hi.
intros j' Hj'.
clear Hi.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with x_1.
apply MF.expo_symm.
tauto.
generalize (between_expf_L0_1 m x y i).
simpl in |- *.
decompose [and] Hj.
assert (MF.f = cF).
tauto.
rewrite <- H19.
fold x_1 in |- *.
rewrite H14.
unfold expf in |- *.
tauto.
decompose [and] Hj'.
assert (MF.f = cF).
clear Hj'.
tauto.
generalize (between_expf_L0_1 m x y i').
simpl in |- *.
fold x_1 in |- *.
rewrite <- H19.
rewrite H14.
unfold expf in |- *.
tauto.
tauto.
tauto.
generalize H0 H16.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
intros.
fold y_0_1 in H8.
generalize (H14 H9 H8).
clear H14.
intro.
elim H14.
intros i Hi.
elim Hi.
intros j Hj.
clear Hi.
clear H14.
elim H17.
intros i' Hi.
clear H17.
elim Hi.
intros j' Hj'.
clear Hi.
assert (MF.f = cF).
tauto.
decompose [and] Hj.
clear Hj.
decompose [and] Hj'.
clear Hj'.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with y_0_1.
apply MF.expo_symm.
tauto.
generalize (between_expf_L0_2 m x y i).
simpl in |- *.
fold y_0_1 in |- *.
rewrite <- H14.
rewrite H17.
unfold expf in |- *.
tauto.
generalize (between_expf_L0_2 m x y i').
simpl in |- *.
fold y_0_1 in |- *.
rewrite <- H14.
rewrite H20.
unfold expf in |- *.
tauto.
tauto.
tauto.
