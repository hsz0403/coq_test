Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma between_expf_L0_2:forall (m:fmap)(x y:dart)(i:nat), inv_hmap (L m zero x y) -> let y_0_1 := cF m y in let x0 := cA m zero x in let z := Iter (cF m) i y_0_1 in betweenf m y_0_1 z x0 -> expf (L m zero x y) y_0_1 z.
Proof.
intros.
induction i.
simpl in z.
unfold z in |- *.
unfold z in H0.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
simpl in |- *.
simpl in H.
unfold prec_L in H.
unfold y_0_1 in |- *.
generalize (exd_cF m y).
tauto.
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
assert (exd m (cA_1 m zero y)).
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
unfold cF in |- *.
generalize (exd_cA_1 m one (cA_1 m zero y)).
tauto.
generalize (H0 H1 H6).
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
rewrite H10 in H0.
rewrite H10 in H9.
induction k.
simpl in H0.
rewrite <- H0 in |- *.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
apply MF.expo_refl.
simpl in |- *.
tauto.
simpl in H0.
set (z_1 := cF_1 m z) in |- *.
assert (z_1 = Iter (cF m) i y_0_1).
unfold z_1 in |- *.
unfold z in |- *.
simpl in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (MF.exd_Iter_f m i y_0_1).
tauto.
assert (z_1 = Iter (cF m) k y_0_1).
unfold z_1 in |- *.
rewrite <- H0 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
rewrite <- H10 in |- *.
generalize (MF.exd_Iter_f m k y_0_1).
tauto.
apply expf_trans with z_1.
rewrite <- H12 in IHi.
apply IHi.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear H14 H15.
split with k.
split with j.
split.
symmetry in |- *.
rewrite H10 in |- *.
tauto.
split.
rewrite H10 in |- *.
tauto.
omega.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
rewrite H12 in |- *.
generalize (MF.exd_Iter_f m i y_0_1).
rewrite H10 in |- *.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H10 in |- *.
unfold cF in |- *.
simpl in |- *.
elim (eq_dart_dec y z_1).
intro.
assert (z = cF m z_1).
unfold z_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold z in |- *.
generalize (MF.exd_Iter_f m (S i) y_0_1).
rewrite H10 in |- *.
tauto.
assert (z = y_0_1).
unfold y_0_1 in |- *.
rewrite a in |- *.
unfold z_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold z in |- *.
generalize (MF.exd_Iter_f m (S i) y_0_1).
rewrite H10 in |- *.
tauto.
assert (S k = 0%nat).
apply (MF.unicity_mod_p m y_0_1 (S k) 0 H1 H6).
omega.
omega.
simpl in |- *.
rewrite H10 in |- *.
rewrite H0 in |- *.
tauto.
inversion H16.
elim (eq_dart_dec (cA m zero x) z_1).
intros.
assert (k = j).
apply (MF.unicity_mod_p m y_0_1 k j H1 H6).
omega.
tauto.
rewrite H10 in |- *.
rewrite H9 in |- *.
rewrite <- H13 in |- *.
symmetry in |- *.
unfold x0 in |- *.
tauto.
absurd (k = j).
omega.
tauto.
intros.
fold (cF m z_1) in |- *.
unfold z_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold z in |- *.
generalize (MF.exd_Iter_f m (S i) y_0_1).
rewrite H10 in |- *.
tauto.
