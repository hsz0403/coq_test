Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma cA_I:forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> x <> z -> (cA (I m x u p) k z = cA m k z).
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
tauto.
Admitted.

Lemma cA_1_I:forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> x <> z -> (cA_1 (I m x u p) k z = cA_1 m k z).
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
tauto.
Admitted.

Lemma expf_refl: forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> expf m z z.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
Admitted.

Lemma expf_symm:forall(m:fmap)(z t:dart), expf m z t -> expf m t z.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
Admitted.

Lemma expf_trans:forall (m : fmap) (z t u : dart), expf m z t -> expf m t u -> expf m z u.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with t.
tauto.
Admitted.

Lemma cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> (cF (I m x u p) z = cF m z).
Proof.
unfold cF in |- *.
intros.
rewrite cA_1_I.
rewrite cA_1_I.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dart_dec x z).
tauto.
intro.
intro.
unfold prec_I in H0.
generalize (exd_cA_1 m zero z).
rewrite <- H3.
Admitted.

Lemma Iter_cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point)(i:nat), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> Iter (cF (I m x u p)) i z = Iter (cF m) i z.
Proof.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
intros.
rewrite IHi.
rewrite cF_I.
tauto.
tauto.
tauto.
assert (MF.f = cF).
tauto.
rewrite <- H3.
generalize (MF.exd_Iter_f m i z).
tauto.
intro.
unfold prec_I in H0.
rewrite H3 in H0.
generalize (MF.exd_Iter_f m i z).
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma expf_I:forall(m:fmap)(x z t:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> (expf (I m x u p) z t <-> expf m z t).
Proof.
intros.
unfold expf in |- *.
unfold MF.expo in |- *.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H3.
split.
intros.
decompose [and] H4.
clear H4.
elim H9.
intros i Eq.
split.
tauto.
split.
tauto.
split with i.
generalize (Iter_cF_I m x z u p i H7 H8 H1 H2).
intro.
rewrite <- H4.
tauto.
intros.
decompose [and] H4.
clear H4.
split.
tauto.
split.
tauto.
elim H8.
intros i Hi.
split with i.
rewrite Iter_cF_I.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cF_L:forall(m:fmap)(k:dim)(x y z:dart), inv_hmap m -> prec_L m k x y -> cF (L m k x y) z = if eq_dim_dec k zero then cA_1 m one (if eq_dart_dec y z then x else if eq_dart_dec (cA m zero x) z then cA_1 m zero y else cA_1 m zero z) else (if eq_dart_dec y (cA_1 m zero z) then x else if eq_dart_dec (cA m one x) (cA_1 m zero z) then cA_1 m one y else cA_1 m one (cA_1 m zero z)).
Proof.
unfold cF in |- *.
intros.
simpl in |- *.
elim (eq_dim_dec k zero).
intro.
elim (eq_dim_dec k one).
intro.
rewrite a0 in a.
inversion a.
tauto.
intro.
elim (eq_dim_dec k one).
tauto.
intro.
induction k.
tauto.
Admitted.

Lemma expf_L0_y_x_1:forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in expf (L m zero x y) y x_1.
Proof.
intros.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
simpl in H.
unfold prec_L in H.
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H0.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y y).
unfold x_1 in |- *.
tauto.
tauto.
tauto.
simpl in H.
tauto.
simpl in H.
Admitted.

Lemma cF_L0_1:forall (m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in betweenf m x_1 z y -> cF (L m zero x y) z = if eq_dart_dec y z then x_1 else cF m z.
Proof.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
assert (exd m (cA_1 m one x)).
generalize (exd_cA_1 m one x).
tauto.
generalize (H0 H1 H).
clear H0.
intro.
elim H0.
intros i Hi.
clear H0.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
clear Hj.
assert (MF.f = cF).
tauto.
rewrite H9 in H0.
rewrite H9 in H8.
rewrite cF_L.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec y z).
tauto.
elim (eq_dart_dec (cA m zero x) z).
intros.
set (p := MF.Iter_upb m (cA_1 m one x)) in |- *.
fold p in H10.
assert (z = Iter (cF m) (p - 1) (cA_1 m one x)).
assert (cF m z = cA_1 m one x).
unfold cF in |- *.
rewrite <- a0.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
assert (z = cF_1 m (cA_1 m one x)).
rewrite <- H11.
rewrite cF_1_cF.
tauto.
tauto.
rewrite <- a0.
generalize (exd_cA m zero x).
tauto.
rewrite H12.
assert (cA_1 m one x = cF m (Iter (cF m) (p - 1) (cA_1 m one x))).
rewrite <- H9.
assert (MF.f m (Iter (MF.f m) (p - 1) (cA_1 m one x)) = Iter (MF.f m) p (cA_1 m one x)).
assert (p = S (p - 1)).
omega.
rewrite H13.
simpl in |- *.
assert ((p - 1 - 0)%nat = (p - 1)%nat).
omega.
rewrite H14.
tauto.
rewrite H13.
unfold p in |- *.
set (x_1 := cA_1 m one x) in |- *.
generalize (MF.Iter_upb_period m x_1).
simpl in |- *.
intros.
rewrite H14.
tauto.
tauto.
unfold x_1 in |- *.
tauto.
rewrite H13.
rewrite cF_1_cF.
rewrite <- H13.
tauto.
tauto.
generalize (MF.exd_Iter_f m (p - 1) (cA_1 m one x)).
tauto.
assert (i = (p - 1)%nat).
eapply (MF.unicity_mod_p m (cA_1 m one x)).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H9.
rewrite <- H11.
tauto.
assert (i = j).
omega.
rewrite H13 in H0.
rewrite H8 in H0.
tauto.
unfold cF in |- *.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
Admitted.

Lemma cF_L0_2:forall (m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let y_0_1 := cF m y in let x0 := cA m zero x in betweenf m y_0_1 z x0 -> cF (L m zero x y) z = if eq_dart_dec x0 z then y_0_1 else cF m z.
Proof.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
assert (exd m (cF m y)).
generalize (exd_cF m y).
tauto.
generalize (H0 H1 H).
clear H0.
intro.
elim H0.
intros i Hi.
clear H0.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
clear Hj.
assert (MF.f = cF).
tauto.
rewrite H9 in H0.
rewrite H9 in H8.
rewrite cF_L in |- *.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec y z).
intro.
elim (eq_dart_dec (cA m zero x) z).
rewrite a0 in H7.
tauto.
intro.
set (p := MF.Iter_upb m (cF m y)) in |- *.
fold p in H10.
assert (cF m y = Iter (cF m) p (cF m y)).
rewrite <- H9 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
rewrite H9 in |- *.
tauto.
assert (z = Iter (cF m) (p - 1) (cF m y)).
rewrite <- a0 in |- *.
assert (p = S (p - 1)).
omega.
rewrite H12 in H11.
simpl in H11.
assert (inj_dart (exd m) (cF m)).
apply inj_cF.
tauto.
unfold inj_dart in H13.
apply H13.
tauto.
generalize (MF.exd_Iter_f m (p - 1) (cF m y)).
tauto.
tauto.
assert (j = (j - i + i)%nat).
omega.
generalize H8.
rewrite H13 in |- *.
rewrite <- H9 in |- *.
rewrite MF.Iter_comp in |- *.
rewrite H9 in |- *.
rewrite H0 in |- *.
intro.
assert ((p - 1)%nat = (p - 1 - j + j)%nat).
omega.
generalize H12.
rewrite H15 in |- *.
rewrite <- H9 in |- *.
rewrite MF.Iter_comp in |- *.
rewrite H9 in |- *.
rewrite H8 in |- *.
rewrite <- H14 in |- *.
rewrite <- H9 in |- *.
rewrite <- MF.Iter_comp in |- *.
intro.
assert (p = MF.Iter_upb m z).
rewrite <- H0 in |- *.
unfold p in |- *.
apply MF.period_uniform.
tauto.
tauto.
clear H13.
clear a.
clear H15.
assert ((p - 1 - j + (j - i))%nat = (p - 1 - i)%nat).
omega.
rewrite H13 in H16.
clear H13.
assert (0%nat = (p - 1 - i)%nat).
apply (MF.unicity_mod_p m z 0 (p - 1 - i)).
tauto.
rewrite <- a0 in |- *.
tauto.
rewrite <- H17 in |- *.
omega.
rewrite <- H17 in |- *.
omega.
rewrite <- H16 in |- *.
simpl in |- *.
tauto.
assert (i = j).
omega.
rewrite H15 in H0.
rewrite <- a0 in H0.
rewrite H8 in H0.
tauto.
elim (eq_dart_dec (cA m zero x) z).
unfold cF in |- *.
tauto.
unfold cF in |- *.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma expf_expf_L0_1:forall (m:fmap)(x y z:dart)(i:nat), inv_hmap (L m zero x y) -> exd m z -> let x_1 := cA_1 m one x in let t := Iter (cF m) i z in expf m x_1 y -> ~ expf m x_1 z -> expf (L m zero x y) z t.
Proof.
intros.
induction i.
simpl in t.
unfold t in |- *.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
simpl in |- *.
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with (Iter (cF m) i z).
simpl in IHi.
unfold expf in IHi.
tauto.
simpl in t.
set (zi := Iter (cF m) i z) in |- *.
fold zi in t.
unfold t in |- *.
assert (MF.f = cF).
tauto.
assert (cF (L m zero x y) zi = cF m zi).
rewrite cF_L.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec y zi).
intro.
rewrite a0 in H1.
elim H2.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_trans with zi.
unfold expf in H1.
tauto.
apply MF.expo_symm.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
tauto.
intro.
elim (eq_dart_dec (cA m zero x) zi).
intro.
assert (expf m x_1 zi).
rewrite <- a0.
unfold x_1 in |- *.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_symm.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
simpl in H.
unfold prec_L in H.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H4.
unfold cF in |- *.
rewrite cA_1_cA.
tauto.
simpl in H.
tauto.
unfold prec_L in H.
simpl in H.
unfold prec_L in H.
tauto.
assert (expf m z zi).
unfold zi in |- *.
unfold expf in |- *.
split.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
rewrite H3.
tauto.
elim H2.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_trans with zi.
unfold expf in H4.
tauto.
apply MF.expo_symm.
simpl in H.
tauto.
unfold expf in H5.
tauto.
unfold cF in |- *.
tauto.
tauto.
simpl in H.
tauto.
simpl in H.
tauto.
rewrite <- H4.
unfold MF.expo in |- *.
simpl in |- *.
split.
unfold zi in |- *.
generalize (MF.exd_Iter_f m i z).
rewrite H3.
simpl in H.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H3.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma expf_L0_x0_y_0_1:forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x0 := cA m zero x in let y_0_1 := cF m y in expf (L m zero x y) x0 y_0_1.
Proof.
intros.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
simpl in H.
unfold prec_L in H.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H0.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y x0).
intros.
simpl in H.
unfold prec_L in H.
symmetry in a.
fold x0 in H.
tauto.
elim (eq_dart_dec (cA m zero x) x0).
intros.
unfold y_0_1 in |- *.
unfold cF in |- *.
tauto.
fold x0 in |- *.
tauto.
tauto.
simpl in H.
tauto.
simpl in H.
tauto.
