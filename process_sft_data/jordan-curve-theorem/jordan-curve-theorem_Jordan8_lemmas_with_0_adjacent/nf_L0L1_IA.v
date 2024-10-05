Require Export Jordan7.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.

Lemma nf_L0L1_IA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> expf m x' y'0 -> expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> cA_1 m zero y <> y' -> x <> y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
elim (eq_dart_dec (cA_1 m zero y) y').
tauto.
fold y'0 in |- *.
tauto.
rewrite H7 in H2.
assert (x_1b = cA_1 (L m one x' y') one x).
fold x_1b in |- *.
tauto.
simpl in H8.
fold x'1 in H8.
elim (eq_dart_dec x'1 x).
intro.
set (y'_1 := cA_1 m one y') in |- *.
fold y'_1 in H8.
assert (x_1b = y'_1).
rewrite H8 in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
assert (x' = x_1).
unfold x_1 in |- *; rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
unfold m1 in H; simpl in H; tauto.
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
clear H8.
rewrite H9 in H3.
assert (betweenf m x_1 y'0 y).
generalize (expf_L0_CNS m x y x' y'0).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
set (x0 := cA m zero x) in |- *.
elim (expf_dec m x_1 y).
intros.
assert (expf (L m zero x y) x' y'0 <-> betweenf m x_1 x' y /\ betweenf m x_1 y'0 y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0 x0 \/ ~ expf m x_1 x' /\ expf m x' y'0).
unfold m1 in H; simpl in H; unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
clear H8.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0 y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0 x0 \/ ~ expf m x_1 x' /\ expf m x' y'0).
tauto.
clear H11.
elim H8.
clear H8.
tauto.
clear H8.
intro.
elim H8.
clear H8.
intro.
absurd (betweenf m y_0_1 x' x0).
rewrite H10 in |- *.
unfold betweenf in |- *.
unfold MF.between in |- *.
intro.
elim H11.
intros i Hi.
elim Hi.
intros j Hj.
decompose [and] Hj.
clear H11 Hi Hj.
set (p := MF.Iter_upb m y_0_1) in |- *.
fold p in H16.
assert (i <> 0).
intro.
rewrite H11 in H12.
simpl in H12.
generalize H12.
unfold y_0_1 in |- *.
unfold x_1 in |- *.
unfold y_0 in |- *.
intro.
assert (x = cA m one x_1).
unfold x_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
unfold m1 in H; simpl in H; tauto.
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
assert (cA m zero x = y).
rewrite H17 in |- *.
unfold x_1 in |- *.
rewrite <- H15 in |- *.
rewrite cA_cA_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
unfold m1 in H; simpl in H; tauto.
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
unfold m1 in H; simpl in H; tauto.
generalize (exd_cA_1 m zero y).
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
assert (i <> p - 1).
intro.
assert (j = p - 1).
omega.
rewrite H17 in H14.
rewrite <- MF.Iter_f_f_1 in H14.
unfold p in H14.
rewrite MF.Iter_upb_period in H14.
simpl in H14.
assert (MF.f_1 = cF_1).
tauto.
rewrite H18 in H14.
unfold y_0_1 in H14.
unfold cF_1 in H14.
rewrite cA_cA_1 in H14.
unfold y_0 in H14.
rewrite cA_cA_1 in H14.
symmetry in H14.
unfold x0 in H14.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
generalize (exd_cA_1 m zero y).
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
unfold y_0_1 in |- *; unfold y_0 in |- *.
fold (cF m y) in |- *.
generalize (exd_cF m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold y_0_1 in |- *; unfold y_0 in |- *.
fold (cF m y) in |- *.
generalize (exd_cF m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
omega.
assert (i - 1 = j).
apply (MF.unicity_mod_p m y_0_1 (i - 1) j).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold y_0_1 in |- *; unfold y_0 in |- *.
fold (cF m y) in |- *.
generalize (exd_cF m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite H14 in |- *.
rewrite H12 in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H17 in |- *.
unfold x_1 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
fold x0 in |- *.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
unfold y_0_1 in |- *; unfold y_0 in |- *.
fold (cF m y) in |- *.
generalize (exd_cF m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
omega.
omega.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold y_0_1 in |- *; unfold y_0 in |- *.
fold (cF m y) in |- *.
generalize (exd_cF m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
tauto.
clear H8.
intro.
absurd (expf m x_1 x').
tauto.
rewrite H10 in |- *.
apply expf_refl.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
rewrite <- H10 in |- *.
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
tauto.
assert (inv_hmap (L m one x' y')).
unfold m2 in H6.
simpl in H6.
simpl in |- *.
tauto.
assert (exd m y'_1).
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
generalize (expf_L1_CNS m x' y' y'_1 y H11 H12).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
fold y'_1 in |- *.
elim (expf_dec m x' y'0).
intro.
intro.
elim H3.
rewrite a in H13.
set (x0 := cA m zero x) in |- *.
fold x0 in H13.
assert (betweenf m y'_1 y x0).
clear H3.
unfold betweenf in H8.
unfold MF.between in H8.
elim H8.
intros i Hi.
elim Hi.
intros j Hj.
decompose [and] Hj.
clear Hi Hj H13.
set (p := MF.Iter_upb m x_1) in |- *.
clear H8.
assert (i <> j).
intro.
rewrite H8 in H3.
assert (y'0 = y).
rewrite <- H3 in |- *.
tauto.
elim H4.
rewrite <- H13 in |- *.
unfold y'0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
unfold m1 in H; simpl in H; tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
rename H8 into Dij.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (j - i - 1).
split with (p - 1 - i - 1).
assert (p = MF.Iter_upb m y'_1).
unfold p in |- *.
assert (expf m x_1 y'_1).
rewrite <- H10 in |- *.
apply expf_trans with y'0.
tauto.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H16 in |- *.
unfold cF in |- *.
unfold y'0 in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
apply MF.period_expo.
tauto.
unfold expf in H16.
tauto.
rewrite <- H16 in |- *.
split.
assert (y'_1 = Iter (MF.f m) 1 y'0).
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H18 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
rewrite H18 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (j - i - 1 + 1 = j - i).
omega.
rewrite H19 in |- *.
clear H19.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (j - i + i = j).
omega.
rewrite H19 in |- *.
tauto.
split.
assert (y'_1 = Iter (MF.f m) 1 y'0).
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H18 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
rewrite H18 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
fold p in H17.
assert (p - 1 - i - 1 + 1 + i = p - 1).
omega.
rewrite H19 in |- *.
clear H19.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H19 in |- *.
unfold cF_1 in |- *.
unfold x_1 in |- *.
rewrite cA_cA_1 in |- *.
fold x0 in |- *.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
generalize (exd_cA_1 m one x).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
omega.
split.
fold p in H17.
omega.
fold p in H17.
omega.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
assert (betweenf m y'_1 y'_1 x0).
unfold betweenf in |- *.
assert (expf m y'_1 x0).
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
simpl in H11.
tauto.
unfold MF.expo in |- *.
split.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H15 in |- *.
unfold y'0 in |- *.
unfold y'_1 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
simpl in H11.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H16 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
unfold m1 in H; simpl in H; unfold prec_L in H; tauto.
apply expf_trans with y'0.
apply expf_symm.
tauto.
apply expf_trans with x'.
apply expf_symm.
tauto.
rewrite H10 in |- *.
apply expf_symm.
tauto.
assert (MF.expo1 m y'_1 x0).
generalize (MF.expo_expo1 m y'_1 x0).
unfold expf in H15.
simpl in H11.
tauto.
generalize (MF.between_expo_refl_1 m y'_1 x0).
unfold expf in H15.
unfold MF.expo in H15.
tauto.
tauto.
tauto.
intro.
assert (x_1b = x_1).
rewrite H8 in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
elim (eq_dart_dec x'1 x).
tauto.
fold x_1 in |- *.
tauto.
rewrite H9 in H3.
clear H8.
generalize (expf_L0_CNS m x y x' y'0).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
set (x0 := cA m zero x) in |- *.
elim (expf_dec m x_1 y).
intros.
assert (expf (L m zero x y) x' y'0 <-> betweenf m x_1 x' y /\ betweenf m x_1 y'0 y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0 x0 \/ ~ expf m x_1 x' /\ expf m x' y'0).
unfold m1 in H; simpl in H; unfold m2 in H6; simpl in H6; unfold prec_L in H6; tauto.
clear H8.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0 y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0 x0 \/ ~ expf m x_1 x' /\ expf m x' y'0).
tauto.
clear a.
clear H10.
elim H3.
clear H3.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold m2 in H6.
simpl in H6.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
generalize (expf_L1_CNS m x' y' x_1 y H3 H10).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
fold x'10 in |- *.
fold y'_1 in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
fold y_0 in H4.
assert (x' <> x_1).
intro.
unfold x'1 in b.
rewrite H12 in b.
unfold x_1 in b.
rewrite cA_cA_1 in b.
tauto.
simpl in H3.
tauto.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
assert (y'0 <> y).
intro.
unfold y_0 in H4.
rewrite <- H13 in H4.
unfold y'0 in H4.
rewrite cA_1_cA in H4.
tauto.
simpl in H3; tauto.
simpl in H3; unfold prec_L in H3.
tauto.
assert (inv_hmap m).
simpl in H3.
tauto.
assert (cF m y'0 = y'_1).
unfold y'0 in |- *.
unfold y'_1 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
simpl in H3.
unfold prec_L in H3.
tauto.
assert (cF_1 m x' = x'10).
unfold x'10 in |- *.
unfold x'1 in |- *.
fold (cF_1 m x') in |- *.
tauto.
elim H8.
clear H8.
intro.
generalize (betweenf1 m x' y'0 x_1 y H14 H10 H12 H13 H8).
rewrite H15 in |- *.
rewrite H16 in |- *.
tauto.
intro.
clear H8.
elim H17.
clear H17.
intro.
assert (y_0_1 = cF m y).
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = cF_1 m x_1).
unfold x0 in |- *.
unfold cF_1 in |- *.
unfold x_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
assert (exd m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
generalize (betweenf2 m x' y'0 x_1 y H14 H19 H12 H13).
rewrite <- H17 in |- *.
rewrite <- H18 in |- *.
rewrite H15 in |- *.
rewrite H16 in |- *.
tauto.
clear H17.
intro.
decompose [and] H8.
clear H8.
assert (~ expf m x' x_1).
intro.
elim H17.
apply expf_symm.
tauto.
tauto.
tauto.
tauto.
