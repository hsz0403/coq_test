Require Export Jordan7.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.

Lemma nf_L0L1_I:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> expf m x' y'0 -> expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> False.
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
simpl in y'0b.
elim (eq_dart_dec x y').
intro.
assert (y'0b = y).
unfold y'0b in |- *.
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
assert (betweenf m x_1 x' y).
generalize (expf_L0_CNS m x y x' y).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
intro.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y y \/ betweenf m (cA_1 m one y_0) x' (cA m zero x) /\ betweenf m (cA_1 m one y_0) y (cA m zero x) \/ ~ expf m x_1 x' /\ expf m x' y).
unfold m1 in H.
simpl in H.
generalize H7.
elim (expf_dec m x_1 y).
assert (exd m x').
unfold m2 in H4.
simpl in H4.
unfold prec_L in H4.
tauto.
tauto.
tauto.
clear H7.
elim H8.
tauto.
intros.
clear H8.
elim H7.
intros.
clear H7.
decompose [and] H8.
clear H8.
unfold betweenf in H9.
unfold MF.between in H9.
assert (inv_hmap m).
unfold expf in H1.
tauto.
assert (exd m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
assert (exd m (cA_1 m one y_0)).
unfold y_0 in |- *.
fold (cF m y) in |- *.
generalize (exd_cF m y).
tauto.
assert (exists i : nat, exists j : nat, Iter (MF.f m) i (cA_1 m one y_0) = y /\ Iter (MF.f m) j (cA_1 m one y_0) = cA m zero x /\ i <= j < MF.Iter_upb m (cA_1 m one y_0)).
tauto.
clear H9.
elim H12.
clear H12.
intros i Hi.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
assert (cA_1 m one y_0 = cF m y).
unfold y_0 in |- *.
tauto.
rewrite H14 in H15.
rewrite H14 in H13.
rewrite H14 in H9.
set (p := MF.Iter_upb m (cF m y)) in |- *.
fold p in H15.
assert (i = p - 1).
apply (MF.unicity_mod_p m (cF m y) i (p - 1)).
unfold m1 in H.
simpl in |- *.
tauto.
assert (exd m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
generalize (exd_cF m y).
unfold m1 in H; simpl in H.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H9 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
rewrite cF_1_cF in |- *.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H.
tauto.
omega.
assert (j = p - 1).
omega.
rewrite H16 in H9.
rewrite H17 in H13.
rewrite H9 in H13.
unfold m1 in H; simpl in H; unfold prec_L in H.
symmetry in H13.
tauto.
intro.
clear H7.
unfold y'0 in H1.
rewrite <- a in H1.
assert (expf m x_1 (cA m zero x)).
assert (x_1 = cF m (cA m zero x)).
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
apply expf_symm.
rewrite H7 in |- *.
unfold expf in |- *.
split.
unfold m1 in H; simpl in H.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_cA m zero x).
assert (inv_hmap m).
unfold m1 in H; simpl in H.
tauto.
assert (exd m x).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
tauto.
split with 1.
simpl in |- *.
tauto.
absurd (expf m x_1 x').
tauto.
apply expf_trans with (cA m zero x).
tauto.
apply expf_symm.
tauto.
elim H3.
assert (exd m x').
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
assert (inv_hmap (L m one x' y')).
unfold m2 in H4.
simpl in H4.
simpl in |- *.
tauto.
generalize (expf_L1_CNS m x' y' x' y H9 H8).
simpl in |- *.
intro.
assert (expf (L m one x' y') x' y <-> betweenf m x' x' (cA m zero y') /\ betweenf m x' y (cA m zero y') \/ betweenf m (cA_1 m one y') x' (cA m zero (cA m one x')) /\ betweenf m (cA_1 m one y') y (cA m zero (cA m one x')) \/ ~ expf m x' x' /\ expf m x' y).
generalize H10.
elim (expf_dec m x' (cA m zero y')).
tauto.
clear H10.
tauto.
clear H10.
clear H3.
assert (betweenf m x' y (cA m zero y')).
rewrite <- a in |- *.
set (x0 := cA m zero x) in |- *.
unfold betweenf in H7.
unfold MF.between in H7.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
assert (exd m x).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
generalize (H7 H3 H13).
intro.
clear H7.
elim H14.
intros i Hi.
elim Hi.
intros j Hj.
clear Hi H14.
decompose [and] Hj.
clear Hj.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H17.
assert (p = MF.Iter_upb m x').
unfold p in |- *.
apply (MF.period_expo m x_1 x' H3).
rewrite <- H7 in |- *.
unfold MF.expo in |- *.
split.
tauto.
split with i.
tauto.
rewrite <- H16 in |- *.
split with (j - i).
split with (p - i - 1).
split.
rewrite <- H7 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (j - i + i = j).
clear H11.
omega.
rewrite H18 in |- *.
tauto.
split.
rewrite <- H7 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - i - 1 + i = p - 1).
clear H11.
omega.
rewrite H18 in |- *.
assert (x0 = Iter (MF.f_1 m) 1 x_1).
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H19 in |- *.
unfold cF_1 in |- *.
unfold x0 in |- *.
unfold x_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
rewrite H19 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H11.
omega.
clear H11.
omega.
assert (betweenf m x' x' (cA m zero y')).
simpl in H9.
generalize (MF.between_expo_refl_1 m x' (cA m zero y')).
intros.
fold y'0 in H10.
unfold expf in H1.
unfold betweenf in |- *.
fold y'0 in |- *.
assert (MF.expo1 m x' y'0).
generalize (MF.expo_expo1 m x' y'0).
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m zero y) y').
intros.
assert (y'0b = cA m zero x).
unfold y'0b in |- *.
elim (eq_dart_dec x y').
tauto.
elim (eq_dart_dec (cA_1 m zero y) y').
tauto.
tauto.
set (x0 := cA m zero x) in |- *.
fold y_0 in a.
assert (y'0 = y).
unfold y'0 in |- *.
rewrite <- a in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
unfold m1 in H; simpl in m1.
simpl in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
set (y_0_1 := cA_1 m one y_0) in |- *.
assert (betweenf m y_0_1 x' x0).
fold x0 in H5.
rewrite H5 in H2.
generalize (expf_L0_CNS m x y x' x0).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold y_0_1 in |- *.
fold x0 in |- *.
intro.
assert (betweenf m x_1 x' y /\ betweenf m x_1 x0 y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 x0 x0 \/ ~ expf m x_1 x' /\ expf m x' x0).
unfold m1 in H.
simpl in H.
assert (exd m x').
unfold m2 in H4.
simpl in H4.
unfold prec_L in H4.
tauto.
generalize H7.
elim (expf_dec m x_1 y).
tauto.
tauto.
clear H7.
elim H8.
intro.
clear H8.
decompose [and] H7.
clear H7.
unfold betweenf in H9.
unfold MF.between in H9.
assert (inv_hmap m).
unfold expf in H1.
tauto.
assert (exd m x).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
elim H9.
clear H9.
intros i Hi.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H15.
assert (x_1 = cF m x0).
unfold x_1 in |- *.
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
assert (i = p - 1).
apply (MF.unicity_mod_p m x_1 i (p - 1)).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H9 in |- *.
unfold p in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite MF.Iter_upb_period in |- *.
rewrite H14 in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H16 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
tauto.
tauto.
tauto.
tauto.
fold p in |- *.
omega.
assert (j = p - 1).
omega.
rewrite H16 in H9.
rewrite H17 in H13.
rewrite H9 in H13; unfold x0 in H13.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
tauto.
tauto.
intro.
clear H8.
elim H7.
clear H7.
intro.
tauto.
clear H7.
intro.
absurd (expf m x_1 x').
tauto.
apply expf_trans with y.
tauto.
apply expf_symm.
rewrite <- H6 in |- *.
tauto.
elim H3.
simpl in x_1b.
assert (cA m one x' <> x).
intro.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- H8 in |- *.
rewrite cA_1_cA in |- *.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
rewrite H9 in H7.
assert (inv_hmap m).
unfold m1 in H; simpl in H.
tauto.
assert (exd m y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
generalize (exd_cF m y).
tauto.
unfold betweenf in H7.
unfold MF.between in H7.
elim H7.
intros i Hi.
elim Hi; intros j Hj.
clear Hi.
clear H7.
decompose [and] Hj.
clear Hj.
set (p := MF.Iter_upb m y_0_1) in |- *.
fold p in H16.
assert (x_1 = cF m x0).
unfold x0 in |- *.
unfold x_1 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
rewrite H15 in H7.
elim (eq_nat_dec i (p - 1)).
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
tauto.
tauto.
tauto.
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
intro.
assert (i <> 0).
intro.
rewrite H17 in H7.
simpl in H7.
generalize H7.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
intros.
assert (x0 = y).
rewrite <- (cF_1_cF m y) in |- *.
rewrite H18 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
unfold x0 in |- *.
generalize (exd_cA m zero x).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
tauto.
tauto.
unfold x0 in H19.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
assert (j = i - 1).
apply (MF.unicity_mod_p m y_0_1 j (i - 1)).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H14 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite H7 in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H18 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
unfold x0 in |- *.
generalize (exd_cA m zero x).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
tauto.
tauto.
omega.
omega.
tauto.
tauto.
assert (x_1b = x_1).
unfold x_1b in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0; tauto.
elim (eq_dart_dec (cA m one x') x).
tauto.
fold x_1 in |- *.
tauto.
rewrite H9 in |- *.
generalize (expf_L1_CNS m x' y' x_1 y).
assert (inv_hmap (L m one x' y')).
unfold m2 in H4.
simpl in H4.
simpl in |- *.
tauto.
assert (exd m x).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
simpl in H10.
tauto.
intro.
simpl in H13.
fold y'0 in H13.
fold x'1 in H13.
assert (expf (L m one x' y') x_1 y <-> betweenf m x' x_1 y'0 /\ betweenf m x' y y'0 \/ betweenf m (cA_1 m one y') x_1 (cA m zero x'1) /\ betweenf m (cA_1 m one y') y (cA m zero x'1) \/ ~ expf m x' x_1 /\ expf m x_1 y).
generalize H13.
elim (expf_dec m x' y'0).
tauto.
tauto.
clear H13.
assert (betweenf m x' x_1 y'0).
rewrite H6 in |- *.
unfold betweenf in H7.
unfold MF.between in H7.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
simpl in H10.
tauto.
elim H7.
clear H7.
intros i Hi.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
set (p := MF.Iter_upb m y_0_1) in |- *.
fold p in H19.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (j - i + 1).
split with (p - 1 - i).
assert (i <> 0).
intro.
rewrite H21 in H7.
simpl in H7.
assert (cA m one x' = y').
rewrite <- H7 in |- *.
unfold y_0_1 in |- *.
rewrite a in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
unfold m2 in H4; simpl in H4; unfold prec_L in H4.
tauto.
assert (p = MF.Iter_upb m x').
unfold p in |- *.
apply (MF.period_expo m y_0_1 x').
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
apply H7.
rewrite <- H22 in |- *.
split.
assert (j - i + 1 = S (j - i)).
clear H14.
omega.
rewrite <- H7 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (j - i + 1 + i = S j).
clear H14.
omega.
rewrite H24 in |- *.
clear H23 H24.
simpl in |- *.
rewrite H17 in |- *.
unfold x_1 in |- *.
unfold x0 in |- *.
assert (MF.f = cF).
tauto.
rewrite H23 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
split.
rewrite <- H7 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - i + i = p - 1).
clear H14.
omega.
rewrite H23 in |- *.
clear H23.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H23 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H14.
omega.
split.
elim (eq_nat_dec j (p - 1)).
intro.
rewrite a0 in H17.
rewrite <- MF.Iter_f_f_1 in H17.
simpl in H17.
unfold p in H17.
rewrite MF.Iter_upb_period in H17.
assert (x0 = y).
rewrite <- H17 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H23 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
unfold x0 in H23.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H14.
omega.
intros.
clear H14.
omega.
clear H14.
omega.
simpl in H10.
tauto.
tauto.
assert (betweenf m x' y y'0).
rewrite H6 in |- *.
unfold betweenf in |- *.
generalize (MF.between_expo_refl_2 m x' y).
assert (MF.expo1 m x' y).
rewrite H6 in H1.
generalize (MF.expo_expo1 m x' y).
simpl in H10.
unfold expf in H1.
tauto.
simpl in H10.
unfold prec_L in H10.
tauto.
tauto.
apply (nf_L0L1_IA m x y x' y' H H0 H1 H2 H3).
