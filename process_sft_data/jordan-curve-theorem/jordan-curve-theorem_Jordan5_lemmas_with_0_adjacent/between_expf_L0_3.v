Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma between_expf_L0_3:forall (m:fmap)(x y:dart)(i:nat), inv_hmap (L m zero x y) -> let x0 := cA m zero x in let x_1 := cA_1 m one x in let z := Iter (cF m) i x_1 in ~ expf m x_1 y -> betweenf m x_1 z x0 -> expf (L m zero x y) x_1 z.
Proof.
intros.
induction i.
simpl in z.
unfold z in |- *.
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
generalize H1.
clear H1.
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
fold x_1 in H.
generalize (H1 H2 H).
clear H1.
intro.
elim H1.
clear H1.
intros k Hk.
elim Hk.
clear Hk.
intros j Hj.
decompose [and] Hj.
clear Hj.
assert (MF.f = cF).
tauto.
rewrite H10 in H1.
rewrite H10 in H9.
induction k.
simpl in H1.
rewrite <- H1.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
apply MF.expo_refl.
simpl in |- *.
tauto.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
apply MF.expo_trans with (Iter (cF m) i x_1).
simpl in IHi.
assert (expf (L m zero x y) x_1 (Iter (cF m) i x_1)).
apply IHi.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with k.
split with j.
split.
unfold z in H1.
simpl in H1.
assert (cF_1 m (cF m (Iter (cF m) k x_1)) = cF_1 m (cF m (Iter (cF m) i x_1))).
rewrite H1.
tauto.
rewrite cF_1_cF in H14.
rewrite cF_1_cF in H14.
tauto.
tauto.
rewrite <- H10.
generalize (MF.exd_Iter_f m i x_1).
tauto.
tauto.
rewrite <- H10.
generalize (MF.exd_Iter_f m k x_1).
tauto.
split.
tauto.
omega.
unfold expf in H12.
tauto.
unfold z in |- *.
simpl in |- *.
set (zi := Iter (cF m) i x_1) in |- *.
elim (eq_dart_dec x0 zi).
intro.
simpl in IHi.
fold zi in IHi.
rewrite <- a in IHi.
rewrite <- a.
unfold cF in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
rewrite <- H12.
fold x_1 in |- *.
assert (expf (L m zero x y) x_1 x0).
apply IHi.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with j.
split with j.
rewrite H10.
split.
tauto.
split.
tauto.
omega.
unfold expf in H13.
apply MF.expo_symm.
tauto.
tauto.
intro.
assert (cF (L m zero x y) zi = cF m zi).
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y zi).
intros.
rewrite a in H0.
elim H0.
unfold zi in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
tauto.
elim (eq_dart_dec (cA m zero x) zi).
fold x0 in |- *.
tauto.
unfold cF in |- *.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
rewrite <- H12.
unfold MF.expo in |- *.
simpl in |- *.
split.
unfold zi in |- *.
generalize (MF.exd_Iter_f m i x_1).
tauto.
split with 1%nat.
simpl in |- *.
rewrite H10.
tauto.
