Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma expf_L1_II_CN:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in expf m x y0 -> expf (L m one x y) z t -> ( betweenf m x z y0 /\ betweenf m x t y0 \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10 \/ ~ expf m x z /\ expf m z t ).
Proof.
intros.
elim (expf_dec m x z).
intro.
set (m1 := L m one x y) in |- *.
fold m1 in H2.
assert (inv_hmap (L m one x y)).
tauto.
simpl in H3.
unfold prec_L in H3.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
tauto.
unfold expf in H2.
decompose [and] H2.
clear H5.
assert (MF.expo1 m1 z t).
generalize (MF.expo_expo1 m1 z t).
fold m1 in H.
tauto.
unfold MF.expo1 in H5.
set (dz1 := MF.Iter_upb m1 z) in |- *.
fold dz1 in H5.
decompose [and] H5.
clear H5 H7.
assert (MF.f = cF).
tauto.
elim H8.
intros it1 Hi.
clear H8.
decompose [and] Hi.
clear Hi.
assert (MF.expo1 m x y0).
unfold expf in H1.
generalize (MF.expo_expo1 m x y0).
tauto.
assert (MF.expo1 m x z).
unfold expf in a.
generalize (MF.expo_expo1 m x z).
tauto.
unfold MF.expo1 in H9.
elim H9.
intros.
clear H11.
clear H9.
elim H12.
intros j0 Hj.
elim Hj.
intros.
clear Hj H12.
set (p := MF.Iter_upb m x) in |- *.
fold p in H9.
unfold MF.expo1 in H10.
elim H10.
intros.
clear H12.
elim H13.
intros iz Hi.
decompose [and] Hi.
clear Hi H13.
fold p in H12.
assert (p = MF.degree m x).
unfold p in |- *.
apply (MF.upb_eq_degree m x).
tauto.
tauto.
clear H10.
clear H6.
assert (j0 + 1 <> p).
intro.
assert (Iter (MF.f m) (j0 + 1) x = y_1).
assert (S j0 = j0 + 1).
omega.
rewrite <- H10 in |- *.
clear H10.
simpl in |- *.
rewrite H11 in |- *.
rewrite H5 in |- *.
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
tauto.
rewrite H6 in H10.
unfold p in H10.
rewrite MF.Iter_upb_period in H10.
assert (cA m one x = y).
rewrite H10 in |- *.
unfold y_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
set (p1 := MF.Iter_upb m1 x) in |- *.
assert (MF.Iter_upb m1 x = MF.degree m1 x).
apply (MF.upb_eq_degree m1 x).
unfold m1 in |- *.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
assert (MF.degree m x = MF.degree m1 x + MF.degree m1 y_1).
unfold m1 in |- *.
unfold y_1 in |- *.
apply degree_L1_split.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in H15.
fold p1 in H10.
rewrite <- H10 in H15.
assert (p1 = j0 + 1).
rewrite H10 in |- *.
unfold m1 in |- *.
apply degree_L1_split_x_y0.
fold y0 in |- *.
symmetry in |- *.
tauto.
tauto.
rewrite <- H13 in |- *.
omega.
fold y0 in |- *.
tauto.
elim (le_lt_dec iz j0).
intro.
assert (Iter (MF.f m1) iz x = z).
unfold m1 in |- *.
rewrite H5 in |- *.
rewrite (cF_L1_x_y0 m x y iz j0) in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
assert (p1 = dz1).
unfold p1 in |- *.
unfold dz1 in |- *.
apply MF.period_expo.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
split with iz.
tauto.
elim (le_lt_dec (iz + it1) j0).
intro.
rewrite <- H17 in H8.
rewrite <- MF.Iter_comp in H8.
assert (Iter (MF.f m) (it1 + iz) x = t).
rewrite H5 in |- *.
rewrite <- (cF_L1_x_y0 m x y (it1 + iz) j0) in |- *.
fold m1 in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *; tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
left.
unfold betweenf in |- *.
unfold MF.between in |- *.
split.
intros.
fold p in |- *.
split with iz.
split with j0.
split.
tauto.
split.
tauto.
omega.
intros.
split with (it1 + iz).
split with j0.
split.
tauto.
split.
tauto.
fold p in |- *.
omega.
intro.
set (it := iz + it1 - (j0 + 1)) in |- *.
assert (Iter (MF.f m) it x = t).
rewrite H5 in |- *.
rewrite <- (cF_L1_x_y0 m x y it j0) in |- *.
fold m1 in |- *.
unfold it in |- *.
rewrite <- H16 in |- *.
rewrite <- H5 in |- *.
rewrite <- (MF.Iter_plus_inv m1 x p1 (iz + it1 - p1)) in |- *.
assert (p1 + (iz + it1 - p1) = iz + it1).
omega.
rewrite H19 in |- *.
clear H19.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
rewrite H17 in |- *.
tauto.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
unfold p1 in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
unfold it in |- *.
omega.
left.
unfold betweenf in |- *.
unfold MF.between in |- *.
fold p in |- *.
split.
intros.
split with iz.
split with j0.
split.
tauto.
split.
tauto.
omega.
intros.
split with it.
split with j0.
split.
tauto.
split.
tauto.
unfold it in |- *.
omega.
intro.
assert (Iter (MF.f m1) (iz - (j0 + 1)) y_1 = z).
unfold m1 in |- *.
rewrite H5 in |- *.
unfold y_1 in |- *.
rewrite (cF_L1_y_1_x10 m x y (iz - (j0 + 1)) j0) in |- *.
assert (j0 + 1 + (iz - (j0 + 1)) = iz).
omega.
rewrite H17 in |- *.
clear H17.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
rewrite <- H13 in |- *.
omega.
set (p2 := MF.Iter_upb m1 y_1) in |- *.
assert (p2 = MF.degree m1 y_1).
unfold p2 in |- *.
apply (MF.upb_eq_degree m1).
tauto.
tauto.
rewrite <- H18 in H15.
assert (p2 = dz1).
unfold p1 in |- *.
unfold dz1 in |- *.
unfold p2 in |- *.
apply MF.period_expo.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
split with (iz - (j0 + 1)).
tauto.
set (iz1 := iz - (j0 + 1)) in |- *.
elim (le_lt_dec (iz + it1) (p - 1)).
intro.
rewrite <- H17 in H8.
rewrite <- MF.Iter_comp in H8.
fold iz1 in H8.
assert (Iter (MF.f m) (j0 + 1 + (it1 + iz1)) x = t).
rewrite H5 in |- *.
rewrite <- (cF_L1_y_1_x10 m x y (it1 + iz1) j0) in |- *.
fold y_1 in |- *.
fold m1 in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
fold y0 in |- *.
fold y0 in |- *.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *; tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
rewrite <- H13 in |- *.
unfold iz1 in |- *.
omega.
assert (Iter (MF.f m) (S j0) x = y_1).
simpl in |- *.
rewrite H11 in |- *.
rewrite H5 in |- *.
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
tauto.
assert (j0 + 1 + (it1 + iz1) = it1 + iz1 + S j0).
omega.
rewrite H22 in H20.
clear H22.
assert (iz = iz1 + S j0).
unfold iz1 in |- *.
omega.
rewrite H22 in H14.
rewrite MF.Iter_comp in H14.
rewrite H21 in H14.
rewrite MF.Iter_comp in H20.
rewrite H21 in H20.
right.
left.
unfold betweenf in |- *.
assert (p = MF.Iter_upb m y_1).
unfold p in |- *.
apply MF.period_expo.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with (S j0).
tauto.
unfold MF.between in |- *.
split.
intros.
rewrite <- H23 in |- *.
split with iz1.
split with (p - 1 - (j0 + 1)).
split.
tauto.
split.
rewrite <- H21 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j0 + 1) + S j0 = p - 1).
omega.
rewrite H26 in |- *.
clear H26.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
fold (cF_1 m x) in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
unfold iz1 in |- *.
omega.
intros.
split with (it1 + iz1).
split with (p - 1 - (j0 + 1)).
rewrite <- H23 in |- *.
split.
tauto.
split.
rewrite <- H21 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j0 + 1) + S j0 = p - 1).
omega.
rewrite H26 in |- *.
clear H26.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
fold (cF_1 m x) in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
omega.
unfold iz1 in |- *.
intro.
assert (Iter (MF.f m1) (it1 + (iz - (j0 + 1))) y_1 = t).
rewrite MF.Iter_comp in |- *.
rewrite H17 in |- *.
tauto.
assert (Iter (MF.f m1) (it1 + (iz - (j0 + 1)) - p2) y_1 = t).
rewrite <- (MF.Iter_plus_inv m1 y_1 p2 (it1 + (iz - (j0 + 1)) - p2)) in |- *.
assert (p2 + (it1 + (iz - (j0 + 1)) - p2) = it1 + (iz - (j0 + 1))).
omega.
rewrite H21 in |- *.
tauto.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
unfold p2 in |- *.
apply MF.Iter_upb_period.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
assert (Iter (MF.f m) (j0 + 1 + (iz - (j0 + 1))) x = z).
rewrite H5 in |- *.
rewrite <- (cF_L1_y_1_x10 m x y (iz - (j0 + 1)) j0) in |- *.
fold y_1 in |- *.
fold m1 in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
rewrite <- H13 in |- *.
omega.
assert (Iter (MF.f m) (j0 + 1 + (it1 + (iz - (j0 + 1)) - p2)) x = t).
rewrite H5 in |- *.
rewrite <- (cF_L1_y_1_x10 m x y (it1 + (iz - (j0 + 1)) - p2) j0) in |- *.
fold y_1 in |- *.
fold m1 in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold m1 in H.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
rewrite <- H13 in |- *.
omega.
right.
left.
assert (Iter (MF.f m) (j0 + 1) x = y_1).
assert (S j0 = j0 + 1).
omega.
rewrite <- H24 in |- *.
clear H24.
simpl in |- *.
rewrite H11 in |- *.
rewrite H5 in |- *.
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
tauto.
assert (j0 + 1 + (iz - (j0 + 1)) = iz - (j0 + 1) + (j0 + 1)).
omega.
rewrite H25 in H22.
clear H25.
assert (j0 + 1 + (it1 + (iz - (j0 + 1)) - p2) = it1 + (iz - (j0 + 1)) - p2 + (j0 + 1)).
omega.
rewrite H25 in H23.
clear H25.
rewrite MF.Iter_comp in H23.
rewrite H24 in H23.
rewrite MF.Iter_comp in H22.
rewrite H24 in H22.
assert (Iter (MF.f m) (p - 1 - (j0 + 1)) y_1 = x10).
rewrite <- H24 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j0 + 1) + (j0 + 1) = p - 1).
omega.
rewrite H25 in |- *.
clear H25.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H25 in |- *.
unfold cF_1 in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
assert (p = MF.Iter_upb m y_1).
unfold p in |- *.
apply MF.period_expo.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with (j0 + 1).
tauto.
unfold betweenf in |- *.
unfold MF.between in |- *.
split.
intros.
rewrite <- H26 in |- *.
split with (iz - (j0 + 1)).
split with (p - 1 - (j0 + 1)).
split.
tauto.
split.
tauto.
omega.
intros.
rewrite <- H26 in |- *.
split with (it1 + (iz - (j0 + 1)) - p2).
split with (p - 1 - (j0 + 1)).
split.
tauto.
split.
tauto.
omega.
intro.
right.
right.
split.
tauto.
apply (expf_L1_II_CNA m x y z t H H0 H1 H2 b).
