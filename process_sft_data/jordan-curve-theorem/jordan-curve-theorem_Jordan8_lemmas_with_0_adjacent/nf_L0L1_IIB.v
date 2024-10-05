Require Export Jordan7.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.

Lemma nf_L0L1_IIB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x <> y' -> y_0 = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
elim (eq_dart_dec (cA_1 m zero y) y').
tauto.
tauto.
assert (x_1b = cA_1 (L m one x' y') one x).
fold x_1b in |- *.
tauto.
generalize H8.
clear H8.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
elim (eq_dart_dec (cA m one x') x).
fold x'1 in |- *.
set (y'_1 := cA_1 m one y') in |- *.
intros.
rewrite H7 in H2.
rewrite H8 in H3.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold m2 in H6.
simpl in H6.
tauto.
assert (inv_hmap m).
simpl in H9.
tauto.
assert (exd m x').
simpl in H9; unfold prec_L in H9.
tauto.
assert (exd m x).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
assert (exd m y).
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
assert (exd m y').
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
assert (exd m y'_1).
generalize (exd_cA_1 m one y').
unfold y'_1 in |- *.
tauto.
generalize (expf_L1_CNS m x' y' y'_1 y H9 H15).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
fold y'_1 in |- *.
elim (expf_dec m x' y'0).
intros.
clear a0.
assert (betweenf m x' y'_1 y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 y'_1 x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' y'_1 /\ expf m y'_1 y).
tauto.
clear H16.
clear H3.
elim H2.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold m1 in H.
simpl in H.
tauto.
generalize (expf_L0_CNS m x y x' x0 H3 H11).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intro.
clear a0.
intro.
elim (eq_dart_dec x' x0).
intro.
rewrite <- a0 in |- *.
apply expf_refl.
tauto.
simpl in |- *.
tauto.
intro.
clear H2.
clear b.
elim H17.
intro.
decompose [and] H2.
clear H2 H17.
unfold betweenf in H18.
unfold MF.between in H18.
elim H18.
intros i Hi.
elim Hi.
intros j Hj.
decompose [and] Hj.
clear Hj Hi H18.
assert (i <> 0).
intro.
rewrite H18 in H2.
simpl in H2.
assert (x'1 = y').
unfold x'1 in |- *.
rewrite H2 in |- *.
unfold y'_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
rewrite a in H21.
tauto.
assert (y'_1 = cF m y'0).
unfold y'_1 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
assert (MF.f = cF).
tauto.
set (p := MF.Iter_upb m x') in |- *.
assert (S j <> p).
intro.
assert (Iter (MF.f m) (S j) x' = x').
rewrite H24 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
simpl in H25.
rewrite H20 in H25.
rewrite H23 in H25.
rewrite <- H21 in H25.
unfold y'_1 in H25.
assert (y' = x'1).
unfold x'1 in |- *.
rewrite <- H25 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
rewrite a in H26.
symmetry in H26.
tauto.
assert (S j = i).
apply (MF.unicity_mod_p m x' (S j) i).
tauto.
tauto.
fold p in |- *.
fold p in H22.
clear H16.
omega.
fold p in |- *.
fold p in H22.
clear H16.
omega.
rewrite H2 in |- *.
simpl in |- *.
rewrite H20 in |- *.
rewrite H23 in |- *.
symmetry in |- *.
tauto.
absurd (S j = i).
clear H16.
omega.
tauto.
tauto.
tauto.
clear H17.
intro.
elim H2.
clear H2.
intro.
decompose [and] H2.
clear H2.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
assert (y'_1 = y_0_1).
unfold y'_1 in |- *.
rewrite <- H5 in |- *.
fold y_0_1 in |- *.
tauto.
rewrite H19 in H18.
rewrite H2 in H18.
assert (y_0_1 = cF m y).
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
unfold betweenf in H18.
unfold MF.between in H18.
assert (exd m y_0_1).
rewrite H20 in |- *.
generalize (exd_cF m y).
tauto.
generalize (H18 H10 H21).
intro.
clear H18.
elim H22.
intros i Hi.
elim Hi.
intros j Hj.
decompose [and] Hj.
clear Hj Hi H22.
set (p := MF.Iter_upb m y_0_1) in |- *.
fold p in H26.
assert (i = p - 1).
apply (MF.unicity_mod_p m y_0_1 i (p - 1)).
tauto; tauto.
tauto.
fold p in |- *.
clear H16.
omega.
fold p in |- *.
clear H16.
omega.
rewrite H18 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H22 in |- *.
rewrite H20 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H16.
omega.
assert (i = j).
clear H16.
omega.
rewrite H25 in H18.
rewrite H24 in H18.
unfold x0 in H18.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
clear H2.
intro.
absurd (expf m x' y'_1).
tauto.
apply expf_trans with y'0.
tauto.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
split with 1.
simpl in |- *.
unfold y'0 in |- *.
assert (MF.f = cF).
tauto.
rewrite H17 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
fold x_1 in H8.
rewrite H8 in H3.
rewrite H7 in H2.
fold x'1 in b.
clear b0.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold m2 in H6.
simpl in H6.
tauto.
assert (inv_hmap m).
simpl in H9.
tauto.
assert (exd m x').
simpl in H9; unfold prec_L in H9.
tauto.
assert (exd m x).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
assert (exd m y).
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
assert (exd m y').
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
assert (exd m x_1).
generalize (exd_cA_1 m one x).
unfold x_1 in |- *.
tauto.
generalize (expf_L1_CNS m x' y' x_1 y H9 H15).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (betweenf m x' x_1 y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1 x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1 /\ expf m x_1 y).
tauto.
clear H16.
clear H3.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold m1 in H.
simpl in H.
tauto.
generalize (expf_L0_CNS m x y x' x0 H3 H11).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intro.
clear a.
intro.
elim H2.
clear H2.
elim (eq_dart_dec x' x0).
intro.
simpl in |- *.
rewrite <- a in |- *.
apply expf_refl.
tauto.
simpl in |- *.
tauto.
intro.
elim H17.
clear H17.
intros.
decompose [and] H2.
clear H2.
unfold betweenf in H17.
unfold MF.between in H17.
elim (H17 H10 H11).
intros i1 Hi.
elim Hi.
intros j1 Hj.
decompose [and] Hj.
clear Hj Hi H17.
unfold betweenf in H18.
unfold MF.between in H18.
elim (H18 H10 H11).
intros i2 Hi.
elim Hi.
intros j2 Hj.
decompose [and] Hj.
clear Hj Hi H18.
set (p := MF.Iter_upb m x') in |- *.
fold p in H25.
fold p in H22.
assert (betweenf m y_0_1 x' x0).
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
assert (S j1 <> p).
intro.
assert (Iter (MF.f m) (S j1) x' = x').
assert (MF.f = cF).
tauto.
rewrite H26 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
simpl in H27.
rewrite H20 in H27.
unfold y'0 in H27.
rewrite <- H5 in H27.
assert (MF.f m (cA m zero y_0) = cF m (cA m zero y_0)).
tauto.
rewrite H27 in H28.
unfold cF in H28.
rewrite cA_1_cA in H28.
rewrite H5 in H28.
simpl in H9.
unfold prec_L in H9.
rewrite H28 in H9.
rewrite cA_cA_1 in H9.
tauto.
tauto.
tauto.
tauto.
generalize (exd_cA_1 m zero y).
unfold y_0 in |- *.
tauto.
assert (expf m x' y_0_1).
assert (y'0 = y).
unfold y'0 in |- *.
rewrite <- H5 in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
assert (MF.f m y = cF m y).
tauto.
rewrite H28 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
apply expf_trans with y'0.
tauto.
rewrite H27 in |- *.
tauto.
assert (p = MF.Iter_upb m y_0_1).
unfold p in |- *.
apply MF.period_expo.
tauto.
unfold expf in H27.
tauto.
rewrite <- H28 in |- *.
assert (i1 <> 0).
intro.
rewrite H29 in H2.
simpl in H2.
unfold x'1 in b.
rewrite H2 in b.
unfold x_1 in |- *.
unfold x_1 in b.
rewrite cA_cA_1 in b.
tauto.
tauto.
tauto.
split with (p - (j1 + 1)).
split with (p - (j1 + 1) + (i1 - 1)).
split.
assert (y_0_1 = cF m y).
unfold y_0_1 in |- *.
unfold cF in |- *.
fold y_0 in |- *.
tauto.
assert (cF m y = Iter (cF m) 1 y).
simpl in |- *.
tauto.
rewrite H30 in |- *.
rewrite H31 in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H32 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (y'0 = y).
unfold y'0 in |- *.
rewrite <- H5 in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
rewrite <- H33 in |- *.
rewrite <- H20 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - (j1 + 1) + 1 + j1 = p).
clear H16.
omega.
rewrite H34 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
split.
assert (y'0 = y).
unfold y'0 in |- *.
rewrite <- H5 in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = cF m y).
unfold y_0_1 in |- *.
unfold cF in |- *.
fold y_0 in |- *.
tauto.
assert (cF m y = Iter (cF m) 1 y).
simpl in |- *.
tauto.
rewrite H31 in |- *.
assert (cF = MF.f).
tauto.
rewrite H32 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H30 in |- *.
rewrite <- H20 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - (j1 + 1) + (i1 - 1) + 1 + j1 = p + (i1 - 1)).
clear H16.
omega.
rewrite H34 in |- *.
clear H34.
assert (x0 = Iter (MF.f m) (i1 - 1) x').
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite H2 in |- *.
assert (MF.f_1 m x_1 = cF_1 m x_1).
tauto.
rewrite H34 in |- *.
unfold x_1 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H16.
omega.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
clear H16.
omega.
assert (expf m y_0_1 x0).
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
unfold x_1 in |- *.
assert (MF.f m x0 = cF m x0).
tauto.
rewrite H26 in |- *.
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
apply expf_trans with y.
apply expf_symm.
tauto.
apply expf_trans with x_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
assert (betweenf m y_0_1 x0 x0).
generalize (MF.between_expo_refl_2 m y_0_1 x0).
assert (exd m y_0_1).
unfold expf in H24.
unfold MF.expo in H24.
tauto.
assert (MF.expo1 m y_0_1 x0).
generalize (MF.expo_expo1 m y_0_1 x0).
unfold expf in H24.
tauto.
tauto.
tauto.
intro.
clear H17.
elim H2.
clear H2.
intro.
decompose [and] H2.
clear H2.
assert (y'0 = y).
unfold y'0 in |- *.
rewrite <- H5 in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = cF m y).
unfold y_0_1 in |- *.
unfold cF in |- *.
fold y_0 in |- *.
tauto.
assert (cF m y = Iter (cF m) 1 y).
simpl in |- *.
tauto.
assert (y'_1 = y_0_1).
unfold y_0_1 in |- *.
rewrite H5 in |- *.
fold y'_1 in |- *.
tauto.
assert (exd m y'_1).
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
tauto.
assert (y <> x'10).
intro.
unfold y_0 in H5.
assert (x'1 = y').
rewrite <- H5 in |- *.
rewrite H23 in |- *.
unfold x'10 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold x'1 in |- *.
generalize (exd_cA m one x').
tauto.
unfold x'1 in |- *.
simpl in H9.
unfold prec_L in H9.
unfold x'1 in H24.
tauto.
unfold betweenf in H18.
unfold MF.between in H18.
elim (H18 H10 H22).
intros i Hi.
elim Hi.
intros j Hj.
decompose [and] Hj.
clear Hj Hi H18.
set (p := MF.Iter_upb m y'_1) in |- *.
assert (i <> j).
intro.
rewrite H18 in H24.
rewrite H24 in H26.
tauto.
assert (Iter (MF.f m) (p - 1) y'_1 = y).
rewrite H21 in |- *.
rewrite H19 in |- *.
rewrite H20 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 + 1 = p).
fold p in H28.
clear H16.
omega.
rewrite H27 in |- *.
rewrite <- H24 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
tauto.
fold p in H28.
assert (i = p - 1).
apply (MF.unicity_mod_p m y'_1 i (p - 1)).
tauto.
tauto.
fold p in |- *.
clear H16.
omega.
fold p in |- *.
clear H16.
omega.
rewrite H27 in |- *.
tauto.
absurd (i = p - 1).
clear H16.
omega.
tauto.
clear H2.
intro.
assert (y'0 = y).
unfold y'0 in |- *.
rewrite <- H5 in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
absurd (expf m x' x_1).
tauto.
apply expf_trans with y'0.
tauto.
rewrite H17 in |- *.
apply expf_symm.
tauto.
tauto.
tauto.
