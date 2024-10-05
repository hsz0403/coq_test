Require Export Jordan6.

Lemma betweenf1 : forall(m:fmap)(u v u' v':dart), inv_hmap m -> exd m u' -> u <> u' -> v <> v' -> (betweenf m u' u v' /\ betweenf m u' v v') -> (betweenf m u u' v /\ betweenf m u v' v \/ betweenf m (cF m v) u' (cF_1 m u) /\ betweenf m (cF m v) v' (cF_1 m u)).
Proof.
intros.
assert (betweenf m u' u v' /\ betweenf m u' v v').
tauto.
rename H4 into H3'.
unfold betweenf in H3.
unfold MF.between in H3.
decompose [and] H3.
clear H3.
generalize (H4 H H0).
clear H4.
intro.
generalize (H5 H H0).
clear H5.
intros.
elim H3.
clear H3.
intros iu Hiu.
elim Hiu.
clear Hiu.
intros jv' Hiv'.
decompose [and] Hiv'.
clear Hiv'.
elim H4.
clear H4.
intros iv Hiv.
elim Hiv.
clear Hiv.
intros jv'1 Hjv.
decompose [and] Hjv.
clear Hjv.
set (p := MF.Iter_upb m u') in |- *.
fold p in H11.
fold p in H8.
decompose [and] H3'.
clear H3'.
unfold betweenf in H10.
generalize (MF.between_expo m u' u v' H H0 H10).
intro.
unfold betweenf in H12.
generalize (MF.between_expo m u' v v' H H0 H12).
intro.
decompose [and] H13.
decompose [and] H14.
clear H13 H14.
assert (MF.f = cF).
tauto.
assert (MF.expo m u' (cF m v)).
apply MF.expo_trans with v.
tauto.
assert (exd m v).
generalize (MF.expo_exd m u' v).
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
generalize (MF.period_expo m u' u H H15).
intro.
generalize (MF.period_expo m u' (cF m v) H H14).
intro.
fold p in H19.
fold p in H20.
assert (jv' = jv'1).
apply (MF.unicity_mod_p m u').
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
tauto.
rewrite H6 in |- *.
rewrite H9 in |- *.
tauto.
assert (iu <> 0%nat).
intro.
rewrite H22 in H3.
simpl in H3.
symmetry in H3.
tauto.
assert (iv <> jv').
intro.
rewrite <- H21 in H9.
rewrite <- H23 in H9.
rewrite H4 in H9.
tauto.
assert (exd m (cF m v)).
generalize (MF.expo_exd m u' v).
generalize (exd_cF m v).
tauto.
elim (le_gt_dec iu iv).
intro.
right.
split.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (p - S iv)%nat.
split with (p - S iv + (iu - 1))%nat.
rewrite <- H20 in |- *.
split.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H20 in |- *.
rewrite MF.Iter_upb_period in |- *.
rewrite MF.Iter_f_1_Si in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite <- H27 in |- *.
rewrite cF_1_cF in |- *.
rewrite <- H4 in |- *.
apply MF.Iter_f_f_1_i.
tauto.
tauto.
tauto.
generalize (exd_cF m v).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
assert (cF_1 = MF.f_1).
tauto.
assert ((p - S iv + (iu - 1))%nat = (p + iu - 1 - S iv)%nat).
omega.
rewrite H28 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite MF.Iter_f_1_Si in |- *.
rewrite <- H13 in |- *.
assert (MF.f m v = Iter (MF.f m) 1 v).
simpl in |- *.
tauto.
rewrite H29 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p + iu - 1 + 1)%nat = S (p + iu - 1)).
omega.
rewrite H30 in |- *.
rewrite MF.f_1_Iter_f in |- *.
rewrite MF.Iter_f_f_1 in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p + iu - 1 - iv + iv)%nat = (p + iu - 1)%nat).
clear H28 H30.
omega.
rewrite H31 in |- *.
rewrite <- H3 in |- *.
assert ((p + iu - 1)%nat = (p + (iu - 1))%nat).
clear H30 H31 H28.
omega.
rewrite H32 in |- *.
rewrite MF.Iter_plus_inv in |- *.
assert (iu = S (iu - 1)).
clear H30 H31 H32.
omega.
rewrite H33 in |- *.
rewrite MF.f_1_Iter_f in |- *.
rewrite <- H33 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
tauto.
generalize (exd_cF m v).
tauto.
clear H28 H30.
omega.
tauto.
generalize (exd_cF m v).
tauto.
tauto.
generalize (MF.exd_Iter_f m (p + iu - 1) (cF m v)).
tauto.
tauto.
tauto.
clear H28.
omega.
omega.
assert (cF_1 = MF.f_1).
tauto.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (jv' - S iv)%nat.
split with (p - S iv + (iu - 1))%nat.
rewrite <- H20 in |- *.
split.
rewrite <- H13 in |- *.
assert (MF.f m v = Iter (MF.f m) 1 v).
simpl in |- *.
tauto.
rewrite H28 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H9 in |- *.
rewrite <- H21 in |- *.
assert ((jv' - S iv + 1 + iv)%nat = jv').
omega.
rewrite H29 in |- *.
tauto.
split.
rewrite <- H13 in |- *.
assert (MF.f m v = Iter (MF.f m) 1 v).
simpl in |- *.
tauto.
rewrite H28 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H3 in |- *.
rewrite H25 in |- *.
assert (iu = S (iu - 1)).
omega.
rewrite H29 in |- *.
rewrite MF.f_1_Iter_f in |- *.
assert ((p - S iv + (S (iu - 1) - 1) + 1 + iv)%nat = (p + (iu - 1))%nat).
clear H29.
omega.
rewrite H30 in |- *.
apply MF.Iter_plus_inv.
tauto.
tauto.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
tauto.
tauto.
omega.
intro.
left.
split.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (p - iu)%nat.
split with (p + iv - iu)%nat.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - iu + iu)%nat = p).
omega.
rewrite H27 in |- *.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
split.
rewrite <- H3 in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p + iv - iu + iu)%nat = (p + iv)%nat).
omega.
rewrite H27 in |- *.
apply MF.Iter_plus_inv.
tauto.
tauto.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
fold p in |- *.
rewrite <- H19 in |- *.
omega.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (jv' - iu)%nat.
split with (p - iu + iv)%nat.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H6 in |- *.
assert ((jv' - iu + iu)%nat = jv').
omega.
rewrite H27 in |- *.
tauto.
split.
rewrite <- H3 in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - iu + iv + iu)%nat = (p + iv)%nat).
omega.
rewrite H27 in |- *.
apply MF.Iter_plus_inv.
tauto.
tauto.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
omega.
