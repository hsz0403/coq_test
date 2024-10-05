Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_expf_L0_4_bis_prel:forall(m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in ~ expf m x_1 y -> expf m y_0_1 z -> expf (L m zero x y) y_0_1 z.
Proof.
intros.
assert (MF.f = cF).
tauto.
rename H2 into McF.
assert (MF.expo1 m y_0_1 z).
unfold expf in H1.
generalize (MF.expo_expo1 m y_0_1 z).
tauto.
unfold MF.expo1 in H2.
decompose [and] H2.
clear H2.
elim H4.
intros i Hi.
clear H4.
decompose [and] Hi.
clear Hi.
rewrite <- H4 in |- *.
rewrite McF in |- *.
generalize (between_expf_L0_4_prel m x y i H H0).
fold y_0 in |- *.
fold y_0_1 in |- *.
rewrite <- McF in |- *.
rewrite H4 in |- *.
intro.
simpl in H.
unfold prec_L in H.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
rename H6 into Exy_0.
assert (betweenf m y_0_1 z y).
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with i.
split with (MF.Iter_upb m y_0_1 - 1)%nat.
split.
tauto.
split.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H8 in |- *.
unfold cF_1 in |- *.
unfold y_0_1 in |- *.
rewrite cA_cA_1 in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
omega.
tauto.
