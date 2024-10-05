Require Export Jordan7.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.

Lemma nf_L0L1_IIC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (y'0b = y'0).
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
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
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
assert (exd m y'0).
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
clear H2.
generalize (expf_L0_CNS m x y x' y'0 H3 H11).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intro.
clear a0.
intro.
elim (eq_dart_dec x' y'0).
intro.
rewrite <- a0 in |- *.
apply expf_refl.
tauto.
simpl in |- *.
tauto.
intro.
elim H17.
intro.
decompose [and] H18.
clear H18 H17.
unfold betweenf in H19.
unfold MF.between in H19.
elim H19.
intros i Hi.
elim Hi.
intros j Hj.
decompose [and] Hj.
clear Hj Hi H19.
set (p := MF.Iter_upb m x') in |- *.
assert (i <> 0).
intro.
rewrite H19 in H17.
simpl in H17.
unfold x'1 in a.
rewrite H17 in a.
unfold y'_1 in a.
rewrite cA_cA_1 in a.
symmetry in a.
tauto.
tauto.
tauto.
assert (y'_1 = cF m y'0).
unfold y'0 in |- *.
unfold cF in |- *; rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
assert (Iter (MF.f m) (p - 1) y'_1 = y'0).
assert (Iter (MF.f m) 1 y'0 = cF m y'0).
simpl in |- *.
tauto.
rewrite H22 in |- *.
rewrite <- H24 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 + 1 = p).
fold p in H23.
clear H2.
omega.
rewrite H25 in |- *.
rewrite <- H21 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
assert (Iter (MF.f m) (j - i) y'_1 = y'0).
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite <- H17 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite MF.Iter_f_f_1 in |- *.
assert (j + i - i = j).
clear H2.
omega.
rewrite H25 in |- *.
clear H25.
tauto.
tauto.
tauto.
clear H2.
omega.
tauto.
tauto.
clear H2.
omega.
assert (p = MF.Iter_upb m y'_1).
unfold p in |- *.
rewrite <- H17 in |- *.
apply MF.period_uniform.
tauto.
tauto.
fold p in H23.
assert (p - 1 = j - i).
apply (MF.unicity_mod_p m y'_1).
tauto.
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
tauto.
rewrite <- H26 in |- *.
clear H2.
omega.
rewrite <- H26 in |- *.
clear H2.
omega.
rewrite H25 in |- *.
tauto.
absurd (p - 1 = j - i).
clear H2.
omega.
tauto.
tauto.
tauto.
intro.
elim H18; intro.
decompose [and] H19.
clear H19 H18 H17.
unfold betweenf in H21.
unfold MF.between in H21.
elim H21.
intros i Hi.
elim Hi.
intros j Hj.
decompose [and] Hj.
clear Hj Hi H21.
set (p := MF.Iter_upb m y'_1) in |- *.
fold p in H23.
assert (x0 <> y'0).
intro.
assert (x = cA_1 m zero y'0).
rewrite <- H21 in |- *.
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H22 in H4.
unfold y'0 in H4.
rewrite cA_1_cA in H4.
tauto.
tauto.
tauto.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
assert (y'_1 = cF m y'0).
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
assert (Iter (cF m) 1 y'0 = y'_1).
simpl in |- *.
symmetry in |- *.
tauto.
assert (Iter (MF.f m) (p - 1) y'_1 = y'0).
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
rewrite H25 in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H27 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H2.
omega.
assert (j <> p - 1).
intro.
rewrite H28 in H19.
rewrite H19 in H27.
rewrite H22 in H27.
tauto.
assert (x_1 = Iter (cF m) 1 x0).
simpl in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (Iter (MF.f m) (S j) y'_1 = x_1).
simpl in |- *.
rewrite H19 in |- *.
rewrite H22 in |- *.
rewrite H29 in |- *.
simpl in |- *.
tauto.
assert (S j <> p - 1).
intro.
rewrite H31 in H30.
rewrite <- H24 in H30.
rewrite H30 in H27.
tauto.
assert (p = MF.Iter_upb m x_1).
unfold p in |- *.
rewrite <- H30 in |- *.
apply MF.period_uniform.
tauto.
tauto.
assert (betweenf m x_1 y'0 y).
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear H33.
split with (p - 1 - (j + 1)).
split with (p - (j + 1) + i).
rewrite <- H32 in |- *.
split.
rewrite <- H30 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j + 1) + S j = p - 1).
clear H2.
omega.
rewrite H33 in |- *.
tauto.
split.
rewrite <- H30 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - (j + 1) + i + S j = p + i).
clear H2.
omega.
rewrite H33 in |- *.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
clear H2.
omega.
assert (betweenf m x_1 x' y).
rewrite H24 in |- *.
unfold betweenf in |- *.
assert (MF.expo1 m x_1 y).
generalize (MF.expo_expo1 m x_1 y).
unfold expf in H0.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
generalize (MF.between_expo_refl_1 m x_1 y).
tauto.
tauto.
tauto.
tauto.
clear H18 H17.
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
assert (MF.f m y'0 = cF m y'0).
tauto.
rewrite H17 in |- *.
unfold cF in |- *.
unfold y'0 in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
absurd (expf m x' y'_1).
tauto.
apply expf_trans with y'0.
tauto.
tauto.
tauto.
tauto.
intros.
fold x_1 in H8.
rewrite H8 in H3.
rewrite H7 in H2.
assert (inv_hmap m).
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
assert (exd m x).
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
assert (exd m y).
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold m1 in H; simpl in H.
tauto.
assert (exd m x').
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
assert (exd m y').
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold m2 in H6; simpl in H6.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
generalize (expf_L1_CNS m x' y' x_1 y H15 H16).
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
clear H17.
clear H3.
elim H2.
generalize (expf_L0_CNS m x y x' y'0 H12 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intro.
clear a.
intro.
assert (y_0_1 = cF m y).
unfold cF in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
tauto.
assert (x0 = cF_1 m x_1).
unfold cF_1 in |- *.
unfold x_1 in |- *.
rewrite cA_cA_1 in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
assert (x_1 <> x').
intro.
unfold x'1 in b.
rewrite <- H20 in b.
unfold x_1 in b.
rewrite cA_cA_1 in b.
tauto.
tauto.
tauto.
assert (y <> y'0).
intro.
unfold y_0 in H5.
rewrite H21 in H5.
unfold y'0 in H5.
rewrite cA_1_cA in H5.
tauto.
tauto.
tauto.
elim H18.
clear H18.
intro.
generalize (betweenf1 m x_1 y x' y'0 H9 H13 H20 H21).
rewrite <- H17 in |- *.
rewrite <- H19 in |- *.
tauto.
intro.
elim H22.
intro.
clear H22 H18.
assert (exd m y'0).
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
generalize (betweenf2 m x_1 y x' y'0 H9 H18 H20 H21).
rewrite <- H17 in |- *.
rewrite <- H19 in |- *.
assert (y'_1 = cF m y'0).
unfold cF in |- *.
unfold y'0 in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
assert (x'10 = cF_1 m x').
unfold cF_1 in |- *.
fold x'10 in |- *.
unfold x'10 in |- *.
unfold x'1 in |- *.
tauto.
rewrite <- H22 in |- *.
rewrite <- H24 in |- *.
tauto.
intro.
clear H22 H18.
decompose [and] H23.
clear H23.
assert (~ expf m x_1 x').
intro.
elim H18.
apply expf_symm.
tauto.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_II:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_IIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_IIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
Admitted.

Lemma nf_L0L1_IIIA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intros.
clear a.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b).
tauto.
clear H6.
elim H1.
clear H1.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in H4.
tauto.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
rewrite H1 in H12.
rewrite H1 in H2.
rewrite H6 in H17.
rewrite H6 in H3.
assert (MF.f = cF).
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
rewrite H18 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H18 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = y'0).
unfold y'0 in |- *.
rewrite <- H4 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H21 in |- *.
rewrite <- H21 in H12.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
elim H12.
clear H12.
intro.
elim H17.
clear H17.
intro.
assert (expf m x_1 x').
generalize (betweenf_expf m x_1 x' y).
tauto.
apply expf_trans with x_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
intro.
clear H17.
elim H25.
clear H25.
intro.
generalize (betweenf_expf m y_0_1 x' x0).
intro.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
tauto.
clear H25.
intro.
absurd (expf m x_1 x').
tauto.
apply expf_symm.
apply expf_trans with y.
tauto.
apply expf_symm.
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m x_1 x' y).
intro.
apply expf_trans with x_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
clear H17.
intro.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m y_0_1 x' x0).
intro.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
tauto.
clear H17.
intro.
absurd (expf m x_1 x').
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_trans with y.
apply expf_symm; tauto.
apply expf_symm; tauto.
clear H12.
tauto.
Admitted.

Lemma nf_L0L1_IIIB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> x <> y' -> y_0 = y' -> False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intros.
clear a.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b).
tauto.
clear H6.
elim H1.
clear H1.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H1 in H17.
rewrite H1 in H3.
simpl in x_1b.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H6 in H12.
rewrite H6 in H2.
assert (MF.f = cF).
tauto.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
rewrite <- H20 in |- *.
rewrite H19 in |- *.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H6 in H12.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
rewrite <- H18 in |- *.
rewrite <- H18 in H12.
assert (MF.f = cF).
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
rewrite H19 in |- *.
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
rewrite H19 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m x_1 x' y).
intro.
apply expf_symm.
apply expf_trans with x_1.
apply expf_symm.
tauto.
tauto.
clear H17.
intro.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m y_0_1 x' x0).
intro.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
apply expf_trans with x0.
tauto.
apply expf_trans with x_1.
tauto.
tauto.
clear H17.
intro.
absurd (expf m x_1 x').
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
Admitted.

Lemma nf_L0L1_IIIC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intros.
clear a.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b).
tauto.
clear H6.
elim H1.
clear H1.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H1 in H17.
rewrite H1 in H3.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H6 in H12.
rewrite H6 in H2.
assert (MF.f = cF).
tauto.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H19 in |- *.
rewrite H19 in H12.
rewrite H19 in H17.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H18 in |- *.
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
rewrite H18 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (expf m y'0 y'_1).
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
rewrite H18 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
elim H12.
clear H12.
intro.
apply expf_trans with y.
tauto.
apply expf_trans with y'_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
apply expf_trans with y.
tauto.
tauto.
clear H12.
intro.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m x_1 y'0 y).
intro.
tauto.
clear H17.
intro.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m y_0_1 x_1 x0).
intro.
generalize (betweenf_expf m y_0_1 y'0 x0).
intro.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
tauto.
clear H17.
intro.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H6 in H12.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y'0 y'_1).
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
rewrite H21 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
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
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m x_1 x' y).
generalize (betweenf_expf m x_1 y'0 y).
intros.
apply expf_trans with x_1.
apply expf_symm.
tauto.
tauto.
clear H17.
intro.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m y_0_1 x' x0).
generalize (betweenf_expf m y_0_1 y'0 x0).
intros.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_III:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_IIIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_IIIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
Admitted.

Lemma nf_L0L1_IVA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intros.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b).
tauto.
clear H6.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in H4.
tauto.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
rewrite H6 in H12.
rewrite H18 in H17.
assert (MF.f = cF).
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
rewrite H19 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H19 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = y'0).
unfold y'0 in |- *.
rewrite <- H4 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H22 in H12.
rewrite <- H22 in H1.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
elim H12.
clear H12.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m x_1 x' y).
intros.
left.
apply expf_trans with x_1.
apply expf_symm.
tauto.
tauto.
intro.
elim H12.
clear H12 H17.
intro.
generalize (betweenf_expf m y_0_1 x' x0).
generalize (betweenf_expf m y_0_1 y x0).
intros.
left.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
tauto.
clear H12.
tauto.
Admitted.

Lemma nf_L0L1_IVB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> x <> y' -> y_0 = y' -> False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intros.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b).
tauto.
clear H6.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H6 in H17.
simpl in x_1b.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a1.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H18 in H12.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = y'_1).
unfold y_0_1 in |- *.
rewrite Eqy in |- *.
fold y'_1 in |- *.
tauto.
rewrite <- H19 in H12.
rewrite <- H20 in H12.
assert (MF.f = cF).
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
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (expf m y_0_1 y).
apply expf_symm.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
fold x_1 in |- *.
tauto.
rewrite H18 in H12.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = y'_1).
unfold y_0_1 in |- *.
rewrite Eqy in |- *.
fold y'_1 in |- *.
tauto.
rewrite <- H19 in H12.
assert (MF.f = cF).
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
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
tauto.
Admitted.

Lemma nf_L0L1_IVC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intros.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b).
tauto.
clear H6.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
tauto.
fold y'0 in |- *.
tauto.
rewrite H6 in H17.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a1.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H18 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a0 in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
assert (MF.f = cF).
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
rewrite H20 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H20 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
split with 1.
simpl in |- *.
rewrite H20 in |- *.
unfold cF in |- *.
unfold y'0 in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
elim H12.
clear H12.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m x_1 y'0 y).
intros.
left.
apply expf_trans with y'0.
apply expf_symm.
tauto.
apply expf_trans with x_1.
apply expf_symm.
tauto.
tauto.
clear H17.
intro.
elim H12.
clear H12.
intro.
rewrite H19 in |- *.
rewrite H19 in H12.
right.
right.
split.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
intro.
rewrite <- H19 in H17.
absurd (expf m x' x').
tauto.
apply expf_refl.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
fold x_1 in |- *.
tauto.
rewrite H18 in H12.
tauto.
assert (MF.f = cF).
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
rewrite H6 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H6 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
Admitted.

Lemma nf_L0L1_IV:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_IVA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_IVB m x y x' y' H H0 H1 H2 H3 b a).
intros.
Admitted.

Lemma nf_L0L1_VB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> ~ expf (L m zero x y) x' y'0b -> x <> y' -> y_0 = y' -> False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intro.
intro.
assert (~ (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b)).
tauto.
clear H6.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H6 in H17.
elim (eq_nat_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a1.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H18 in H12.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = y'_1).
unfold y_0_1 in |- *.
rewrite Eqy in |- *.
fold y'_1 in |- *.
tauto.
assert (MF.f = cF).
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
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (expf m y_0_1 y).
apply expf_symm.
tauto.
rewrite <- H20 in H12.
rewrite <- H19 in H12.
rewrite <- H19 in H1.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
fold x_1 in |- *.
tauto.
rewrite H18 in H12.
tauto.
Admitted.

Lemma nf_L0L1_VC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> ~ expf (L m zero x y) x' y'0b -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intro.
intro.
assert (~ (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b)).
tauto.
clear H6.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
tauto.
fold y'0 in |- *.
tauto.
rewrite H6 in H17.
elim (eq_nat_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a1.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H18 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a0 in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H19 in H12.
rewrite H19 in H17.
assert (MF.f = cF).
tauto.
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
split with 1.
simpl in |- *.
rewrite H20 in |- *.
unfold cF in |- *.
unfold y'0 in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
assert (expf m y x_1 /\ expf m y'_1 y'0).
split.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
fold x_1 in |- *.
tauto.
rewrite H18 in H12.
tauto.
Admitted.

Lemma nf_L0L1_V:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> ~ expf (L m zero x y) x' y'0b -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_VA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_VB m x y x' y' H H0 H1 H2 H3 b a).
intros.
Admitted.

Lemma nf_L0L1_VA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> ~ expf (L m zero x y) x' y'0b -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
intro.
intro.
assert (~ (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b)).
tauto.
clear H6.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in H4.
tauto.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
rewrite H6 in H12.
rewrite H18 in H17.
assert (MF.f = cF).
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
rewrite H19 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
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
rewrite H19 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = y'0).
unfold y'0 in |- *.
rewrite <- H4 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H22 in H12.
rewrite <- H22 in H1.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
elim H12.
right.
left.
split.
apply expf_refl.
tauto.
tauto.
apply expf_trans with x_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
tauto.
