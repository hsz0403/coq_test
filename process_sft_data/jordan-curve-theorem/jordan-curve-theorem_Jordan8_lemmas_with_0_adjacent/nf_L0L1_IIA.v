Require Export Jordan7.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.

Lemma nf_L0L1_IIA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
unfold m1 in |- *.
unfold m2 in |- *.
set (mx := L m zero x y) in |- *.
set (mx' := L m one x' y') in |- *.
unfold nf in |- *.
fold nf in |- *.
unfold mx' in |- *.
fold x_1b in |- *.
unfold mx in |- *.
fold y'0b in |- *.
rename H4 into a.
rename H5 into H4.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
rewrite H5 in H2.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in a.
tauto.
rewrite H6 in H3.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold m2 in H4.
simpl in H4.
tauto.
assert (exd m x').
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
generalize (expf_L1_CNS m x' y' x' y H7 H8).
simpl in |- *.
fold y'0 in |- *.
set (y'_1 := cA_1 m one y') in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
elim (expf_dec m x' y'0).
intros.
clear a0.
assert (betweenf m x' x' y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x' x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x' /\ expf m x' y).
tauto.
clear H9.
elim H2.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold m1 in H.
simpl in H.
tauto.
generalize (expf_L0_CNS m x y x' y H9 H8).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
set (x0 := cA m zero x) in |- *.
elim (expf_dec m x_1 y).
intro.
clear a0.
intro.
elim (eq_nat_dec x' y).
intro.
rewrite a0 in |- *.
apply expf_refl.
tauto.
simpl in |- *.
rewrite <- a0 in |- *.
tauto.
intro.
elim H10.
intros.
clear H10.
decompose [and] H12.
clear H12.
unfold betweenf in H13.
unfold MF.between in H13.
elim H13.
intros i Hi.
elim Hi.
intros j Hj.
decompose [and] Hj.
clear H13 Hi Hj.
assert (betweenf m x_1 x' y).
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim (eq_dart_dec x_1 x').
intro.
rewrite <- a0 in |- *.
split with 0.
split with i.
simpl in |- *.
split.
tauto.
split.
rewrite a0 in |- *.
tauto.
rewrite a0 in |- *.
clear H11.
omega.
intro.
assert (y'0 = x0).
unfold y'0 in |- *.
unfold x0 in |- *.
rewrite a in |- *.
tauto.
set (p := MF.Iter_upb m x') in |- *.
fold p in H17.
assert (j <> p - 1).
intro.
rewrite H19 in H15.
unfold p in H15.
rewrite <- MF.Iter_f_f_1 in H15.
simpl in H15.
rewrite MF.Iter_upb_period in H15.
rewrite H18 in H15.
assert (MF.f_1 = cF_1).
tauto.
rewrite H20 in H15.
assert (x' = cF m x0).
rewrite <- H15 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
unfold cF in H21.
unfold x0 in H21.
rewrite cA_1_cA in H21.
fold x_1 in H21.
symmetry in H21.
tauto.
tauto.
simpl in H19.
simpl in H9; unfold prec_L in H9; tauto.
tauto.
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
tauto.
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
fold p in |- *.
clear H11.
omega.
assert (expf m x' x_1).
apply expf_trans with y'0.
tauto.
rewrite H18 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
simpl in H9; unfold prec_L in H9; tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H20 in |- *.
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
simpl in H9; unfold prec_L in H9; tauto.
assert (p = MF.Iter_upb m x_1).
unfold p in |- *.
apply MF.period_expo.
tauto.
unfold expf in H20.
tauto.
rewrite <- H21 in |- *.
split with (p - (j + 1)).
split with (p + i - (j + 1)).
split.
assert (x_1 = Iter (MF.f m) 1 x0).
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H22 in |- *.
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
simpl in H9; unfold prec_L in H9.
tauto.
rewrite H22 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - (j + 1) + 1 = p - j).
clear H11.
omega.
rewrite H23 in |- *.
rewrite <- H18 in |- *.
rewrite <- H15 in |- *.
rewrite <- MF.Iter_comp in |- *.
clear H23.
assert (p - j + j = p).
clear H11.
omega.
rewrite H23 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
split.
assert (x_1 = Iter (MF.f m) 1 x0).
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H22 in |- *.
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
simpl in H9; unfold prec_L in H9.
tauto.
rewrite H22 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p + i - (j + 1) + 1 = p + i - j).
clear H11.
omega.
rewrite H23 in |- *.
clear H23.
rewrite <- H18 in |- *.
rewrite <- H15 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p + i - j + j = p + i).
clear H11.
omega.
rewrite H23 in |- *.
clear H23.
rewrite MF.Iter_comp in |- *.
rewrite H12 in |- *.
unfold p in |- *.
assert (expf m x' y).
apply expf_trans with y'0.
tauto.
rewrite H18 in |- *.
apply expf_trans with x_1.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
simpl in H9; unfold prec_L in H9.
tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H23 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
simpl in H9; unfold prec_L in H9; tauto.
tauto.
assert (p = MF.Iter_upb m y).
unfold p in |- *.
apply MF.period_expo.
tauto.
unfold expf in H23.
tauto.
fold p in |- *.
rewrite H24 in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
simpl in H9.
unfold prec_L in H9.
tauto.
clear H11.
omega.
assert (betweenf m x_1 y y).
unfold betweenf in |- *.
assert (MF.expo1 m x_1 y).
generalize (MF.expo_expo1 m x_1 y).
unfold expf in H0.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
simpl in H9.
unfold prec_L in H9.
tauto.
generalize (MF.between_expo_refl_2 m x_1 y).
simpl in H7.
tauto.
tauto.
simpl in H7.
tauto.
tauto.
intro.
elim H12.
clear H12.
clear H10.
intro.
decompose [and] H10.
clear H10.
elim (eq_dart_dec x' x_1).
intro.
rewrite a0 in H11.
assert (betweenf m x_1 x_1 y).
unfold betweenf in |- *.
assert (MF.expo1 m x_1 y).
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
simpl in H9.
unfold prec_L in H9.
tauto.
generalize (MF.expo_expo1 m x_1 y).
unfold expf in H0.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
simpl in H9.
unfold prec_L in H9.
tauto.
generalize (MF.between_expo_refl_1 m x_1 y).
simpl in H7.
tauto.
assert (betweenf m x_1 y y).
unfold betweenf in |- *.
assert (MF.expo1 m x_1 y).
generalize (MF.expo_expo1 m x_1 y).
unfold expf in H0.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
simpl in H9.
unfold prec_L in H9.
tauto.
generalize (MF.between_expo_refl_2 m x_1 y).
simpl in H7.
tauto.
rewrite a0 in |- *.
tauto.
intro.
assert (y'_1 = x_1).
unfold x_1 in |- *.
unfold y'_1 in |- *.
rewrite a in |- *.
tauto.
rewrite H10 in H12.
unfold betweenf in H12.
unfold MF.between in H12.
elim H12.
intros i Hi.
elim Hi.
intros j Hj.
elim Hj.
intros.
decompose [and] H15.
clear Hi Hj H12 H15.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H19.
assert (S j <> p).
intro.
assert (Iter (MF.f m) (S j) x_1 = x_1).
rewrite H12 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
simpl in H9; unfold prec_L in H9.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
simpl in H9.
unfold prec_L in H9.
tauto.
tauto.
simpl in H15.
rewrite H16 in H15.
assert (MF.f = cF).
tauto.
rewrite H17 in H15.
unfold cF in H15.
unfold x'10 in H15.
unfold x'1 in H15.
rewrite cA_1_cA in H15.
rewrite cA_1_cA in H15.
tauto.
simpl in H9.
unfold prec_L in H9.
tauto.
tauto.
simpl in H9.
unfold prec_L in H9.
tauto.
simpl in H9.
unfold prec_L in H9.
generalize (exd_cA m one x'); simpl in H9.
unfold prec_L in H9.
tauto.
assert (S j = i).
apply (MF.unicity_mod_p m x_1 (S j) i).
simpl in H9; unfold prec_L in H9.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
simpl in H9.
unfold prec_L in H9.
tauto.
tauto.
fold p in |- *.
clear H11.
omega.
fold p in |- *.
clear H11.
omega.
simpl in |- *.
rewrite H14 in |- *.
rewrite H16 in |- *.
assert (MF.f = cF).
tauto.
rewrite H15 in |- *.
unfold cF in |- *.
unfold x'10 in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
rewrite cA_1_cA in |- *.
tauto.
simpl in H9.
unfold prec_L in H9.
tauto.
tauto.
simpl in H9.
unfold prec_L in H9.
tauto.
generalize (exd_cA m one x'); simpl in H9.
unfold prec_L in H9.
tauto.
absurd (S j = i).
clear H11.
omega.
tauto.
unfold prec_L in H9.
unfold prec_L in H9.
simpl in H9.
tauto.
generalize (exd_cA_1 m one x).
simpl in H9.
unfold prec_L in H9.
tauto.
clear H12.
clear H10.
intro.
absurd (expf m x' x').
tauto.
apply expf_refl.
simpl in H9.
tauto.
tauto.
tauto.
tauto.
