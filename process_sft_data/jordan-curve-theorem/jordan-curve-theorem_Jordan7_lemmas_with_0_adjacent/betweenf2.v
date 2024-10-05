Require Export Jordan6.

Lemma betweenf2:forall(m:fmap)(u v u' v':dart), inv_hmap m -> exd m v' -> u <> u' -> v <> v' -> (betweenf m (cF m v') u (cF_1 m u') /\ betweenf m (cF m v') v (cF_1 m u')) -> (betweenf m u u' v /\ betweenf m u v' v \/ betweenf m (cF m v) u' (cF_1 m u) /\ betweenf m (cF m v) v' (cF_1 m u)).
Proof.
intros.
assert (betweenf m (cF m v') u (cF_1 m u') /\ betweenf m (cF m v') v (cF_1 m u')).
tauto.
rename H4 into H3'.
unfold betweenf in H3.
unfold MF.between in H3.
decompose [and] H3.
clear H3.
assert (exd m (cF m v')).
generalize (exd_cF m v').
tauto.
rename H3 into Ev'1.
generalize (H4 H Ev'1).
clear H4.
intro.
generalize (H5 H Ev'1).
clear H5.
intros.
elim H3.
clear H3.
intros iu Hiu.
elim Hiu.
clear Hiu.
intros iu'_1 Hiu'_1.
decompose [and] Hiu'_1.
clear Hiu'_1.
elim H4.
clear H4.
intros iv Hiv.
elim Hiv.
clear Hiv.
intros iu'_2 Hiu'_2.
decompose [and] Hiu'_2.
clear Hiu'_2.
set (p := MF.Iter_upb m (cF m v')) in |- *.
fold p in H11.
fold p in H8.
decompose [and] H3'.
clear H3'.
unfold betweenf in H10.
generalize (MF.between_expo m (cF m v') u (cF_1 m u') H Ev'1 H10).
intro.
unfold betweenf in H12.
generalize (MF.between_expo m (cF m v') v (cF_1 m u') H Ev'1 H12).
intro.
decompose [and] H13.
decompose [and] H14.
clear H13 H14.
assert (MF.f = cF).
tauto.
assert (iu'_1 = iu'_2).
apply (MF.unicity_mod_p m (cF m v')).
tauto.
tauto.
fold p in |- *.
tauto.
fold p in |- *.
tauto.
rewrite H9 in |- *.
tauto.
rewrite <- H14 in H7.
clear H11 H9 H14.
clear iu'_2.
assert (MF.f_1 = cF_1).
tauto.
elim (eq_nat_dec (p - 1) iv).
intro.
assert (v' = Iter (MF.f m) (p - 1) (cF m v')).
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (exd_cF_1 m v').
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
symmetry in H9.
rewrite a in H11.
rewrite H4 in H11.
symmetry in H11.
tauto.
intro.
assert (exd m (cF_1 m u')).
rewrite <- H6 in |- *.
generalize (MF.exd_Iter_f m iu'_1 (cF m v')).
tauto.
assert (exd m u').
generalize (exd_cF_1 m u').
tauto.
elim (eq_nat_dec (S iu'_1) iu).
intro.
assert (Iter (MF.f m) (S iu'_1) (cF m v') = u').
simpl in |- *.
rewrite H6 in |- *.
rewrite H13 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite a in H19.
rewrite H3 in H19.
tauto.
intro.
set (v'1 := cF m v') in |- *.
fold v'1 in Ev'1.
fold v'1 in H3.
fold v'1 in H6.
fold v'1 in H4.
fold v'1 in p.
fold v'1 in H10.
fold v'1 in H12.
fold v'1 in H15.
fold v'1 in H16.
fold v'1 in H17.
fold v'1 in H18.
set (u'_1 := cF_1 m u') in |- *.
fold u'_1 in H6.
fold u'_1 in H10.
fold u'_1 in H12.
fold u'_1 in H16.
fold u'_1 in H18.
fold u'_1 in H11.
assert (exd m v).
apply MF.expo_exd with v'1.
tauto.
tauto.
assert (exd m (cF m v)).
generalize (exd_cF m v).
tauto.
set (v1 := cF m v) in |- *.
set (u_1 := cF_1 m u) in |- *.
assert (MF.expo m v'1 v1).
apply MF.expo_trans with v.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
unfold v1 in |- *.
tauto.
assert (p = MF.Iter_upb m v1).
unfold MF.expo in H21.
elim H21.
clear H21.
intros.
elim H22.
intros i Hi.
rewrite <- Hi in |- *.
unfold p in |- *.
apply MF.period_uniform.
tauto.
tauto.
elim (le_gt_dec iu iv).
intro.
right.
split.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim (eq_nat_dec iu'_1 (p - 1)).
intro.
assert (u' = v'1).
assert (u' = cF m u'_1).
unfold u'_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite H25 in |- *.
rewrite <- H6 in |- *.
rewrite a0 in |- *.
assert (cF m (Iter (MF.f m) (p - 1) v'1) = Iter (MF.f m) 1 (Iter (MF.f m) (p - 1) v'1)).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H26 in |- *.
clear H26.
rewrite <- MF.Iter_comp in |- *.
assert ((1 + (p - 1))%nat = p).
omega.
rewrite H26 in |- *.
clear H26.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
assert (u <> v'1).
intro.
rewrite <- H25 in H26.
tauto.
assert (iu <> 0%nat).
intro.
rewrite H27 in H3.
simpl in H3.
symmetry in H3.
tauto.
clear H23.
clear H26.
split with (p - S iv)%nat.
split with (p - S iv + iu - 1)%nat.
rewrite <- H22 in |- *.
split.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H22 in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold v1 in |- *.
rewrite <- H4 in |- *.
simpl in |- *.
rewrite H9 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H23 in |- *.
assert (cF_1 m (Iter (cF_1 m) iv (Iter (MF.f m) (S iv) v'1)) = Iter (cF_1 m) (S iv) (Iter (MF.f m) (S iv) v'1)).
simpl in |- *.
tauto.
rewrite H26 in |- *.
rewrite <- H9 in |- *.
rewrite MF.Iter_f_f_1_i in |- *.
assert (u' = cF m u'_1).
unfold u'_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite H28 in |- *.
rewrite <- H6 in |- *.
rewrite a0 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite <- H13 in |- *.
rewrite MF.f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
tauto.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv + iu - 1 + S iv)%nat = (iu - 1 + p)%nat).
omega.
rewrite H26 in |- *.
clear H26.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H3 in |- *.
simpl in |- *.
unfold u_1 in |- *.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
omega.
intro.
elim (eq_nat_dec iu 0).
intro.
assert (u = v'1).
rewrite a0 in H3.
simpl in H3.
symmetry in |- *.
tauto.
split with (S iu'_1 - S iv)%nat.
split with (p - S iv - 1)%nat.
rewrite <- H22 in |- *.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H26 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((S iu'_1 - S iv + S iv)%nat = S iu'_1).
omega.
rewrite H27 in |- *.
clear H27 H26.
simpl in |- *.
rewrite H6 in |- *.
unfold u'_1 in |- *.
rewrite H13 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H26 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv - 1 + S iv)%nat = (p - 1)%nat).
omega.
rewrite H27 in |- *.
clear H27.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
rewrite <- H25 in |- *.
unfold u_1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
omega.
intro.
split with (S iu'_1 - S iv)%nat.
split with (p - S iv + iu - 1)%nat.
rewrite <- H22 in |- *.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H25 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((S iu'_1 - S iv + S iv)%nat = S iu'_1).
omega.
rewrite H26 in |- *.
clear H25 H26.
simpl in |- *.
rewrite H6 in |- *.
unfold u'_1 in |- *.
rewrite H13 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H25 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv + iu - 1 + S iv)%nat = (iu - 1 + p)%nat).
omega.
rewrite H26 in |- *.
clear H26.
clear H25.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H3 in |- *.
simpl in |- *.
unfold u_1 in |- *.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
omega.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H4 in H23.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear H24.
rewrite <- H22 in |- *.
elim (eq_nat_dec iu 0).
split with (p - 1 - S iv)%nat.
split with (p - S iv - 1)%nat.
split.
unfold v1 in |- *.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - 1 - S iv + S iv)%nat = (p - 1)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold v'1 in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (exd_cF m v').
fold v'1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
unfold v1 in |- *.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv - 1 + S iv)%nat = (p - 1)%nat).
omega.
rewrite H24 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold v'1 in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
rewrite a0 in H3.
simpl in H3.
unfold u_1 in |- *.
rewrite <- H3 in |- *.
unfold v'1 in |- *.
rewrite cF_1_cF in |- *.
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
intro.
split with (p - 1 - S iv)%nat.
split with (p - S iv + iu - 1)%nat.
split.
unfold v1 in |- *.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - 1 - S iv + S iv)%nat = (p - 1)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold v'1 in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (exd_cF m v').
fold v'1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
unfold v1 in |- *.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv + iu - 1 + S iv)%nat = (p + (iu - 1))%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H3 in |- *.
simpl in |- *.
unfold u_1 in |- *.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
omega.
intro.
left.
unfold betweenf in |- *.
assert (p = MF.Iter_upb m u).
rewrite <- H3 in |- *.
unfold p in |- *.
apply MF.period_uniform.
tauto.
tauto.
split.
unfold MF.between in |- *.
intros.
clear H24.
split with (iu'_1 + 1 - iu)%nat.
split with (p + iv - iu)%nat.
rewrite <- H23 in |- *.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((iu'_1 + 1 - iu + iu)%nat = S iu'_1).
omega.
rewrite H24 in |- *.
clear H24.
simpl in |- *.
rewrite H6 in |- *.
unfold u'_1 in |- *.
rewrite H13 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p + iv - iu + iu)%nat = (iv + p)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
omega.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear H24.
split with (p - 1 - iu)%nat.
split with (p - iu + iv)%nat.
rewrite <- H23 in |- *.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - 1 - iu + iu)%nat = (p - 1)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold v'1 in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (exd_cF m v').
fold v'1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - iu + iv + iu)%nat = (p + iv)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
tauto.
tauto.
tauto.
omega.
