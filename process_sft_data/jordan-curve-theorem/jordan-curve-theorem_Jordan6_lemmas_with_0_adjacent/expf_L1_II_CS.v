Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma expf_L1_II_CS:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in expf m x y0 -> ( betweenf m x z y0 /\ betweenf m x t y0 \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10 \/ ~ expf m x z /\ expf m z t ) -> expf (L m one x y) z t.
Proof.
intros.
generalize (expf_dec m x z).
generalize (expf_dec m z t).
intros AA BB.
fold (dec (expf m z t)) in AA.
fold (dec (expf m x z)) in BB.
elim (and_not (expf m z t) (expf m x z) AA BB).
intro.
apply expf_not_orbit_x.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
tauto.
intro.
elim H2.
intro.
decompose [and] H3.
clear H3.
unfold betweenf in H4.
unfold MF.between in H4.
simpl in H; unfold prec_L in H.
elim H4.
clear H4.
intros iz Hiz.
elim Hiz.
intros iy01 Hi.
decompose [and] Hi.
clear Hi Hiz.
clear H2.
unfold betweenf in H5.
unfold MF.between in H5.
elim H5.
clear H5.
intros it Hi.
elim Hi.
intros iy02 Hj.
decompose [and] Hj.
clear Hi Hj.
assert (iy01 = iy02).
apply (MF.unicity_mod_p m x).
simpl in H; tauto.
simpl in H; unfold prec_L in H; tauto.
tauto.
tauto.
rewrite H7 in |- *.
tauto.
assert (MF.f = cF).
tauto.
rewrite H11 in H3.
rewrite H11 in H2.
assert (Iter (MF.f m) iy01 x = y0).
tauto.
rename H12 into E1.
assert (Iter (MF.f m) iy02 x = y0).
tauto.
rename H12 into E2.
assert (iy01 <> MF.Iter_upb m x - 1).
intro.
rewrite H12 in H6.
generalize H6.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
intro.
assert (y = cA_1 m zero (MF.f_1 m x)).
rewrite H13 in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
assert (MF.f_1 m x = cF_1 m x).
tauto.
rewrite H15 in H14.
unfold cF_1 in H14.
rewrite cA_1_cA in H14.
symmetry in H14.
tauto.
tauto.
generalize (exd_cA m one x).
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
rewrite <- (cF_L1_x_y0 m x y iz iy01) in H3.
rewrite <- (cF_L1_x_y0 m x y it iy02) in H2.
assert (expf (L m one x y) x z).
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *; tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
tauto.
split with iz.
rewrite H11 in |- *.
rewrite H3 in |- *.
tauto.
assert (expf (L m one x y) x t).
unfold expf in |- *.
split.
simpl in |- *; unfold prec_L in |- *; tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
tauto.
split with it.
rewrite H11 in |- *.
rewrite H2 in |- *.
tauto.
apply expf_trans with x.
apply expf_symm.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- MF.upb_eq_degree in |- *.
omega.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- MF.upb_eq_degree in |- *.
omega.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
elim H3.
intro.
clear H2 H3.
decompose [and] H4.
clear H4.
unfold betweenf in H2.
unfold MF.between in H2.
simpl in H; unfold prec_L in H.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
tauto.
elim H2.
intros iz Hi.
elim Hi.
intros j1 Hj.
decompose [and] Hj.
clear Hi Hj H2.
unfold betweenf in H3.
unfold MF.between in H3.
elim H3.
intros it Hi.
elim Hi.
intros j2 Hj.
decompose [and] Hj.
clear Hj Hi H3.
assert (j1 = j2).
apply (MF.unicity_mod_p m y_1).
tauto.
tauto.
omega.
omega.
rewrite H10 in |- *.
tauto.
assert (MF.f = cF).
tauto.
assert (MF.f_1 = cF_1).
tauto.
assert (Iter (MF.f m) iz y_1 = z).
tauto.
rename H14 into E1.
assert (Iter (MF.f m) it y_1 = t).
tauto.
rename H14 into E2.
assert (MF.Iter_upb m y_1 = MF.degree m y_1).
apply MF.upb_eq_degree.
tauto.
tauto.
set (p := MF.Iter_upb m y_1) in |- *.
fold p in H9.
fold p in H12.
fold p in H14.
assert (MF.expo1 m x y0).
unfold expf in H1.
generalize (MF.expo_expo1 m x y0).
tauto.
unfold MF.expo1 in H15.
decompose [and] H15.
clear H15.
elim H17.
clear H17.
intros j0 Hj0.
elim Hj0.
clear Hj0.
intros.
assert (expf m y0 y_1).
unfold y0 in |- *.
unfold y_1 in |- *.
apply (expf_y0_y_1 m x y).
tauto.
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (expf m x y_1).
apply expf_trans with y0.
tauto.
tauto.
assert (MF.Iter_upb m x = MF.Iter_upb m y_1).
apply MF.period_expo.
tauto.
unfold expf in H19.
tauto.
fold p in H20.
rewrite H20 in H15.
assert (j0 <> p - 1).
rewrite <- H20 in |- *.
intro.
rewrite H21 in H17.
rewrite <- MF.Iter_f_f_1 in H17.
simpl in H17.
rewrite MF.Iter_upb_period in H17.
rewrite H13 in H17.
assert (cA_1 m zero (cF_1 m x) = y).
rewrite H17 in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
unfold cF_1 in H22.
rewrite cA_1_cA in H22.
tauto.
tauto.
generalize (exd_cA m one x).
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite H20 in |- *.
omega.
assert (Iter (cF m) 1 y0 = y_1).
simpl in |- *.
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
tauto.
assert (Iter (cF m) 1 x10 = x).
simpl in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
fold (cF_1 m x) in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite <- H22 in E1.
rewrite <- MF.Iter_comp in E1.
rewrite <- H17 in E1.
rewrite <- MF.Iter_comp in E1.
rewrite <- H22 in E2.
rewrite <- MF.Iter_comp in E2.
rewrite <- H17 in E2.
rewrite <- MF.Iter_comp in E2.
assert (x10 = Iter (MF.f m) (p - 1 - (j0 + 1)) y_1).
rewrite <- H22 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H17 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j0 + 1) + 1 + j0 = p - 1).
omega.
rewrite H24 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite <- H20 in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
fold (cF_1 m x) in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H24.
omega.
assert (p - 1 - (j0 + 1) = j2).
apply (MF.unicity_mod_p m y_1).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
tauto.
rewrite <- H24 in |- *.
symmetry in |- *.
tauto.
assert (iz + 1 + j0 = j0 + 1 + iz).
omega.
rewrite H26 in E1.
clear H26.
assert (it + 1 + j0 = j0 + 1 + it).
omega.
rewrite H26 in E2.
clear H26.
rewrite H11 in E1.
rewrite H11 in E2.
rewrite <- (cF_L1_y_1_x10 m x y iz j0) in E1.
rewrite <- (cF_L1_y_1_x10 m x y it j0) in E2.
fold y_1 in E1.
fold y_1 in E2.
assert (expf (L m one x y) y_1 z).
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
tauto.
split with iz.
tauto.
assert (expf (L m one x y) y_1 t).
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
tauto.
split with it.
tauto.
apply expf_trans with y_1.
apply expf_symm.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
assert (p = MF.degree m x).
unfold p in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold p in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
rewrite <- H26 in |- *.
omega.
assert (p = MF.degree m x).
unfold p in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold p in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
rewrite <- H26 in |- *.
omega.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
assert (p = MF.degree m x).
unfold p in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold p in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
rewrite <- H26 in |- *.
omega.
assert (p = MF.degree m x).
unfold p in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold p in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
rewrite <- H26 in |- *.
omega.
tauto.
tauto.
tauto.
tauto.
intro.
clear H3.
clear H2.
generalize (expf_dec m x z).
generalize (expf_dec m z t).
tauto.
