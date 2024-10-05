Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma between_expf_L0_4_prel:forall(m:fmap)(x y:dart)(i:nat), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in let z := Iter (cF m) i y_0_1 in ~ expf m x_1 y -> betweenf m y_0_1 z y -> expf (L m zero x y) y_0_1 z.
Proof.
intros.
assert (MF.f = cF).
tauto.
rename H2 into McF.
simpl in H.
unfold prec_L in H.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
generalize (exd_cA_1 m one y_0).
unfold y_0_1 in |- *.
tauto.
induction i.
simpl in z.
unfold z in |- *.
apply expf_refl.
simpl in |- *.
unfold prec_L in |- *.
tauto.
simpl in |- *.
tauto.
decompose [and] H.
clear H.
generalize H1.
clear H1.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
intro.
generalize (H1 H4 H3).
clear H1.
intro.
elim H.
clear H.
intros k Hk.
elim Hk.
clear Hk.
intros j Hj.
decompose [and] Hj.
clear Hj.
set (zi := Iter (cF m) i y_0_1) in |- *.
assert (z = cF m zi).
unfold z in |- *.
simpl in |- *.
fold zi in |- *.
tauto.
assert (zi = cF_1 m z).
rewrite H11 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
unfold zi in |- *.
generalize (MF.exd_Iter_f m i y_0_1).
rewrite McF in |- *.
tauto.
elim (eq_dart_dec zi y).
intro.
assert (z = y_0_1).
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
rewrite <- a in |- *.
tauto.
rewrite H14 in |- *.
apply expf_refl.
simpl in |- *.
unfold prec_L in |- *.
tauto.
simpl in |- *.
tauto.
intro.
assert (k <> 0%nat).
intro.
rewrite H14 in H.
simpl in H.
elim b.
clear b.
rewrite H13 in |- *.
rewrite <- H in |- *.
unfold y_0_1 in |- *.
unfold cF_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
fold (cF_1 m (cF m y)) in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
tauto.
assert (zi = Iter (MF.f m) (k - 1) y_0_1).
rewrite H13 in |- *.
rewrite <- H in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite H15 in |- *.
assert (MF.f_1 m (Iter (MF.f m) k y_0_1) = Iter (MF.f_1 m) 1 (Iter (MF.f m) k y_0_1)).
simpl in |- *.
tauto.
rewrite H16 in |- *.
rewrite MF.Iter_f_f_1 in |- *.
tauto.
tauto.
tauto.
omega.
assert (cF (L m zero x y) zi = cF m zi).
rewrite cF_L in |- *.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y zi).
intros.
symmetry in a.
tauto.
intros.
elim (eq_dart_dec (cA m zero x) zi).
intro.
assert (x_1 = z).
rewrite H11 in |- *.
unfold x_1 in |- *.
rewrite <- a0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
elim H0.
rewrite H16 in |- *.
apply expf_trans with y_0_1.
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with k.
tauto.
unfold expf in |- *.
unfold MF.expo in |- *.
split.
tauto.
split.
tauto.
split with j.
tauto.
fold (cF m zi) in |- *.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
apply expf_trans with zi.
apply IHi.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear H17 H18.
split with (k - 1)%nat.
split with j.
rewrite <- H15 in |- *.
fold zi in |- *.
split.
tauto.
split.
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
unfold zi in |- *.
generalize (MF.exd_Iter_f m i y_0_1).
rewrite McF in |- *.
tauto.
split with 1%nat.
simpl in |- *.
rewrite McF in |- *.
rewrite H16 in |- *.
symmetry in |- *.
tauto.
