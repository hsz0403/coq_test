Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_expf_L0_3_bis:forall (m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let x0 := cA m zero x in let x_1 := cA_1 m one x in ~ expf m x_1 y -> expf m x_1 z -> expf (L m zero x y) x_1 z.
Proof.
intros.
assert (MF.expo1 m x_1 z).
unfold expf in H1.
generalize (MF.expo_expo1 m x_1 z).
tauto.
unfold MF.expo1 in H2.
decompose [and] H2.
clear H2.
elim H4.
intros i Hi.
clear H4.
decompose [and] Hi.
clear Hi.
rewrite <- H4.
unfold x_1 in |- *.
apply between_expf_L0_3.
tauto.
fold x_1 in |- *.
tauto.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with i.
split with (MF.Iter_upb m x_1 - 1)%nat.
split.
tauto.
split.
rewrite <- MF.Iter_f_f_1.
fold x_1 in |- *.
rewrite MF.Iter_upb_period.
unfold x_1 in |- *.
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H7.
unfold cF_1 in |- *.
rewrite cA_cA_1.
tauto.
tauto.
simpl in H.
unfold prec_L in H.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
omega.
fold x_1 in |- *.
omega.
