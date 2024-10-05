Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma between_expf_L0_1:forall (m:fmap)(x y:dart)(i:nat), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in let z := Iter (cF m) i x_1 in betweenf m x_1 z y -> expf (L m zero x y) x_1 z.
Proof.
intros.
induction i.
assert (z = x_1).
unfold z in |- *.
simpl in |- *.
tauto.
rewrite H1.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
simpl in |- *.
simpl in H.
unfold prec_L in H.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
simpl in z.
generalize H0.
clear H0.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
intro.
simpl in H.
unfold prec_L in H.
decompose [and] H.
clear H.
assert (exd m (cA_1 m one x)).
generalize (exd_cA_1 m one x).
tauto.
generalize (H0 H1 H).
clear H0.
intro.
elim H0.
clear H0.
intros k Hk.
elim Hk.
intros j Hj.
decompose [and] Hj.
clear Hj.
clear Hk.
assert (MF.f = cF).
tauto.
rewrite H9 in H0.
rewrite H9 in H8.
induction k.
simpl in H0.
rewrite <- H0.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
apply MF.expo_refl.
simpl in |- *.
tauto.
simpl in H0.
assert (cF_1 m z = Iter (cF m) i x_1).
unfold z in |- *.
rewrite cF_1_cF.
tauto.
tauto.
rewrite <- H9.
generalize (MF.exd_Iter_f m i x_1).
tauto.
rewrite <- H0 in H11.
rewrite cF_1_cF in H11.
assert (z = cF m (Iter (cF m) k x_1)).
rewrite H11.
unfold z in |- *.
tauto.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
apply MF.expo_trans with (Iter (cF m) k x_1).
simpl in IHi.
unfold expf in IHi.
rewrite <- H11 in IHi.
assert (betweenf m x_1 (Iter (cF m) k x_1) y).
unfold betweenf in |- *.
unfold MF.between in |- *.
fold x_1 in H.
intros.
clear H14 H13.
split with k.
split with j.
split.
rewrite H9.
tauto.
split.
tauto.
omega.
tauto.
rewrite <- H0.
assert (cF (L m zero x y) (Iter (cF m) k x_1) = cF m (Iter (cF m) k x_1)).
rewrite cF_L0_1.
elim (eq_dart_dec y (Iter (cF m) k x_1)).
intro.
rewrite a in H8.
assert (j = k).
apply (MF.unicity_mod_p m x_1 j k H1).
unfold x_1 in |- *.
tauto.
tauto.
omega.
rewrite H9.
tauto.
absurd (j = k).
omega.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
tauto.
fold x_1 in |- *.
unfold betweenf in |- *.
unfold MF.between in |- *.
fold x_1 in H.
intros.
clear H14 H13.
split with k.
split with j.
split.
rewrite H9.
tauto.
split.
tauto.
omega.
rewrite <- H13.
rewrite <- H9.
unfold MF.expo in |- *.
split.
simpl in |- *.
generalize (MF.exd_Iter_f m k x_1).
unfold x_1 in |- *.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
tauto.
rewrite <- H9.
generalize (MF.exd_Iter_f m k x_1).
unfold x_1 in |- *.
tauto.
