Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_CN_1:forall (m:fmap)(x y z:dart)(i:nat), inv_hmap (L m zero x y) -> exd m z -> let x0 := cA m zero x in let x_1 := cA_1 m one x in let y_0:= cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in let t:= Iter (cF (L m zero x y)) i z in expf m x_1 y -> (betweenf m x_1 z y /\ betweenf m x_1 t y \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t).
Proof.
assert (MF.f = cF).
tauto.
intros.
assert (inv_hmap (L m zero x y)).
tauto.
rename H2 into a.
rename H3 into H2.
simpl in H2.
unfold prec_L in H2.
decompose [and] H2.
clear H2.
induction i.
simpl in t.
unfold t in |- *.
elim (expf_dec m x_1 z).
intro.
assert (MF.expo1 m x_1 y).
unfold expf in a.
generalize (MF.expo_expo1 m x_1 y).
tauto.
assert (MF.expo1 m x_1 z).
unfold expf in a0.
generalize (MF.expo_expo1 m x_1 z).
tauto.
generalize (MF.expo_between_3 m x_1 y z H3 H2 H8).
intro.
elim H10.
left.
unfold betweenf in |- *.
tauto.
right.
left.
unfold x_1 in H11.
unfold betweenf in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
rewrite H in H11.
assert (MF.f_1 = cF_1).
tauto.
rewrite H12 in H11.
unfold cF_1 in H11.
rewrite cA_cA_1 in H11.
unfold cF in H11.
fold x0 in H11.
tauto.
tauto.
tauto.
unfold expf at 3 in |- *.
assert (MF.expo m z z).
apply MF.expo_refl.
tauto.
tauto.
simpl in IHi.
set (zi := Iter (cF (L m zero x y)) i z) in |- *.
fold zi in IHi.
simpl in t.
fold zi in t.
assert (~ expf m x_1 z /\ expf m z t \/ expf m x_1 z \/ ~ expf m z t).
generalize (expf_dec m x_1 z).
generalize (expf_dec m z t).
tauto.
elim H2.
tauto.
clear H2.
intro.
elim IHi.
clear IHi.
intro.
left.
split.
tauto.
unfold t in |- *.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y zi).
intros.
fold x_1 in |- *.
generalize (MF.between_expo_refl_1 m x_1 y H3).
unfold betweenf in |- *.
unfold expf in a.
unfold MF.expo in a.
generalize (MF.between_expo1 m x_1 zi y).
unfold betweenf in H8.
tauto.
elim (eq_dart_dec (cA m zero x) zi).
intros.
fold x0 in a0.
rewrite <- a0 in H8.
absurd (betweenf m x_1 x0 y).
unfold betweenf in |- *.
unfold MF.between in |- *.
intro.
assert (exd m x_1).
unfold expf in a.
unfold MF.expo in a.
tauto.
elim H10.
clear H10.
intros k Hk.
elim Hk.
clear Hk.
intros j Hj.
decompose [and] Hj.
clear Hj.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H15.
assert (Iter (MF.f m) (p - 1) x_1 = x0).
rewrite <- MF.Iter_f_f_1.
unfold p in |- *.
rewrite MF.Iter_upb_period.
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H14.
unfold cF_1 in |- *.
unfold x_1 in |- *.
rewrite cA_cA_1.
unfold x0 in |- *.
tauto.
tauto.
tauto.
tauto.
unfold expf in a.
unfold MF.expo in a.
tauto.
tauto.
unfold expf in a.
unfold MF.expo in a.
tauto.
omega.
assert (k = (p - 1)%nat).
apply MF.unicity_mod_p with m x_1.
tauto.
unfold expf in a.
unfold MF.expo in a.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H10.
symmetry in |- *.
tauto.
rewrite H16 in H12.
assert (j = (p - 1)%nat).
omega.
rewrite H17 in H13.
rewrite H14 in H13.
unfold x0 in H13.
tauto.
tauto.
unfold expf in a.
unfold MF.expo in a.
tauto.
tauto.
intros.
decompose [and] H8.
clear H8.
unfold betweenf in H11.
unfold MF.between in H11.
elim H11.
clear H11.
intros k Hk.
elim Hk.
clear Hk.
intros j Hj.
decompose [and] Hj.
clear Hj.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (k + 1)%nat.
split with j.
split.
assert ((k + 1)%nat = S k).
omega.
rewrite H16.
simpl in |- *.
rewrite H8.
rewrite H.
unfold cF in |- *.
tauto.
simpl in |- *.
split.
tauto.
elim (eq_nat_dec k j).
intro.
rewrite a1 in H8.
rewrite <- H12 in b0.
tauto.
intro.
omega.
tauto.
unfold expf in a.
unfold MF.expo in a.
tauto.
tauto.
tauto.
simpl in H0.
tauto.
intro.
elim H8.
clear H8.
intro.
right.
left.
split.
tauto.
unfold t in |- *.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
rename H10 into Exy0.
assert (MF.f_1 = cF_1).
tauto.
rename H10 into H_1.
set (p := MF.Iter_upb m y_0_1) in |- *.
assert (MF.expo1 m x_1 y).
generalize (MF.expo_expo1 m x_1 y).
unfold expf in a.
tauto.
rename H10 into Exp1.
unfold MF.expo1 in Exp1.
decompose [and] Exp1.
clear Exp1.
elim H11.
clear H11.
intros k Hk.
clear IHi.
decompose [and] Hk.
clear Hk.
rename H11 into Hk.
rename H12 into Hk1.
assert (y = MF.f_1 m y_0_1).
unfold y_0_1 in |- *.
rewrite H_1.
unfold cF_1 in |- *.
rewrite cA_cA_1.
unfold y_0 in |- *.
rewrite cA_cA_1.
tauto.
tauto.
tauto.
tauto.
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (MF.f m (Iter (MF.f m) k x_1) = Iter (MF.f m) (S k) x_1).
simpl in |- *.
tauto.
assert (MF.Iter_upb m x_1 = MF.Iter_upb m y_0_1).
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
assert (x_1 = Iter (MF.f_1 m) k y).
rewrite <- Hk1.
rewrite MF.Iter_f_f_1_i.
tauto.
tauto.
tauto.
rewrite <- Hk1.
rewrite <- H.
rewrite H12.
apply MF.period_uniform.
tauto.
tauto.
fold p in H13.
rewrite H13 in Hk.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y zi).
intros.
fold x_1 in |- *.
unfold betweenf in |- *.
rewrite <- a0 in H8.
absurd (betweenf m y_0_1 y x0).
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
intro.
elim H14.
clear H14.
intros n Hn.
elim Hn.
intros q Hq.
clear Hn.
decompose [and] Hq.
clear Hq.
fold p in H18.
assert (Iter (MF.f m) (p - 1) y_0_1 = y).
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
rewrite <- H.
rewrite <- MF.Iter_f_f_1.
simpl in |- *.
assert (p = MF.Iter_upb m y).
unfold p in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
rewrite <- H.
assert (MF.f m y = Iter (MF.f m) 1 y).
simpl in |- *.
tauto.
rewrite H17.
rewrite (MF.period_uniform m y 1).
tauto.
tauto.
tauto.
assert (Iter (MF.f m) p (MF.f m y) = Iter (MF.f m) (S p) y).
rewrite MF.Iter_f_Si.
tauto.
tauto.
tauto.
rewrite H19.
simpl in |- *.
rewrite H17.
rewrite MF.Iter_upb_period.
apply MF.f_1_f.
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite H.
generalize (exd_cF m y).
tauto.
omega.
rewrite <- H17 in H14.
assert (n = (p - 1)%nat).
apply (MF.unicity_mod_p m y_0_1).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
tauto.
assert (q = (p - 1)%nat).
omega.
rewrite H20 in H16.
rewrite H16 in H17.
unfold x0 in H17.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA m zero x) zi).
intros.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
unfold betweenf in |- *.
generalize (MF.between_expo_refl_1 m (cF m y) x0).
intro.
generalize (MF.expo_expo1 m (cF m y) x0).
intro.
assert (exd m (cF m y)).
generalize (exd_cF m y).
tauto.
cut (MF.expo m (cF m y) x0).
tauto.
apply MF.expo_trans with y.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
apply MF.expo_symm.
tauto.
apply MF.expo_trans with x_1.
unfold x_1 in |- *.
unfold x0 in |- *.
unfold MF.expo in |- *.
split.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
unfold cF in |- *.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
unfold expf in a.
tauto.
intros.
fold (cF m zi) in |- *.
decompose [and] H8.
clear H8.
unfold betweenf in H15.
unfold MF.between in H15.
elim H15.
intros n Hn.
clear H15.
elim Hn.
intros q Hq.
clear Hn.
decompose [and] Hq.
fold p in H18.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear Hq.
split with (S n).
split with q.
split.
simpl in |- *.
rewrite H8.
rewrite H.
tauto.
split.
tauto.
fold p in |- *.
elim (eq_nat_dec n q).
intro.
rewrite a1 in H8.
rewrite H16 in H8.
unfold x0 in H8.
tauto.
intro.
omega.
tauto.
tauto.
tauto.
tauto.
simpl in H0.
tauto.
intros.
clear H8.
clear IHi.
elim H2.
tauto.
intro.
clear H2.
assert (t = cF (L m zero x y) zi).
unfold t in |- *.
tauto.
generalize H2.
clear H2.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y zi).
intros.
fold x_1 in H2.
rewrite <- a0 in H10.
absurd (expf m x_1 z).
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with y.
unfold expf in a.
tauto.
apply MF.expo_symm.
tauto.
unfold expf in H10.
tauto.
elim (eq_dart_dec (cA m zero x) zi).
intros.
fold (cF m y) in H2.
rewrite <- a0 in H10.
fold x0 in H10.
absurd (expf m x_1 z).
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with x0.
apply MF.expo_symm.
tauto.
unfold x_1 in |- *.
unfold x0 in |- *.
unfold MF.expo in |- *.
split.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
unfold cF in |- *.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
apply MF.expo_symm.
tauto.
unfold expf in H10.
tauto.
intros.
fold (cF m zi) in H2.
rewrite H2 in H8.
absurd (expf m z (cF m zi)).
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with zi.
unfold expf in H10.
tauto.
unfold MF.expo in |- *.
split.
unfold zi in |- *.
generalize (MF.exd_Iter_f (L m zero x y) i z).
simpl in |- *.
rewrite H.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
tauto.
tauto.
tauto.
simpl in H0.
tauto.
