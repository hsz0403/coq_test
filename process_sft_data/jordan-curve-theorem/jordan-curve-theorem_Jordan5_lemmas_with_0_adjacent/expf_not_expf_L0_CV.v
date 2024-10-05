Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_not_expf_L0_CV:forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1:= cA_1 m one x in let x0 := cA m zero x in expf (L m zero x y) y x0 -> ~expf m x_1 y.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
tauto.
rename H1 into Inv.
simpl in Inv.
unfold prec_L in Inv.
decompose [and] Inv.
clear Inv.
generalize (expf_L0_CN m x y y x0 H H2 H0).
simpl in |- *.
fold x_1 in |- *.
elim (expf_dec m x_1 y).
intros.
elim H6.
clear H6.
intros.
decompose [and] H6.
clear H6.
generalize H9.
clear H9.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim H9.
intros i Hi.
clear H9.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H12.
assert (Iter (MF.f m) (p - 1) x_1 = x0).
rewrite <- MF.Iter_f_f_1.
unfold p in |- *.
rewrite MF.Iter_upb_period.
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H11.
unfold cF_1 in |- *.
unfold x_1 in |- *.
rewrite cA_cA_1.
fold x0 in |- *.
tauto.
tauto.
tauto.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
omega.
assert (i = (p - 1)%nat).
apply MF.unicity_mod_p with m x_1.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H6.
symmetry in |- *.
tauto.
absurd (i = (p - 1)%nat).
elim (eq_nat_dec i j).
intro.
rewrite a0 in H6.
assert (x0 = y).
rewrite <- H6.
tauto.
unfold x0 in H14.
tauto.
intro.
omega.
tauto.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
clear H6.
intro.
elim H6.
clear H6.
fold x0 in |- *.
fold (cF m y) in |- *.
intro.
decompose [and] H6.
clear H6.
assert (exd m x0).
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
generalize H8.
clear H8.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim H8.
intros i Hi.
clear H8.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
set (y_0_1 := cF m y) in |- *.
fold y_0_1 in H8.
fold y_0_1 in H12.
set (p := MF.Iter_upb m (cF m y)) in |- *.
fold p in H14.
fold y_0_1 in p.
assert (Iter (MF.f m) (p - 1) y_0_1 = y).
rewrite <- MF.Iter_f_f_1.
unfold p in |- *.
rewrite MF.Iter_upb_period.
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H13.
unfold cF_1 in |- *.
unfold y_0_1 in |- *.
unfold cF in |- *.
rewrite cA_cA_1.
rewrite cA_cA_1.
tauto.
tauto.
tauto.
tauto.
generalize (exd_cA_1 m zero y).
tauto.
tauto.
unfold y_0_1 in |- *.
generalize (exd_cF m y).
tauto.
tauto.
unfold y_0_1 in |- *.
generalize (exd_cF m y).
tauto.
omega.
assert (i = (p - 1)%nat).
apply MF.unicity_mod_p with m y_0_1.
tauto.
unfold y_0_1 in |- *.
generalize (exd_cF m y).
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H13.
tauto.
elim (eq_nat_dec i j).
intro.
rewrite a0 in H8.
rewrite H12 in H8.
unfold x0 in H8.
tauto.
intro.
elim b.
omega.
tauto.
generalize (exd_cF m y).
tauto.
clear H6.
tauto.
tauto.
