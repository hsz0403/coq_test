Require Export Jordan6.

Theorem expf_not_expf_B0: forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let x_1:= cA_1 m one x in let x0 := cA m zero x in let xb0 := bottom m zero x in (expf (B m zero x) x_1 x0 <-> ~expf m x0 xb0).
Proof.
intros.
split.
intro.
generalize (expf_B0_CN m x x_1 x0 H H0 H1).
simpl in |- *.
fold x_1 in |- *.
fold xb0 in |- *.
fold x0 in |- *.
set (xh0 := top m zero x) in |- *.
set (xh0_1 := cA_1 m one xh0) in |- *.
elim (expf_dec m x0 xb0).
intros.
elim H2; clear H2.
intro.
elim H2.
clear H2.
intros.
elim (eq_dart_dec x0 xb0).
intro.
unfold x0 in a0.
unfold xb0 in a0.
generalize a0.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
intros.
symmetry in a2.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
unfold betweenf in H3.
unfold MF.between in H3.
elim H3.
intros i Hi.
clear H3.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H7.
assert (x0 = Iter (cF m) (p - 1) x_1).
unfold x_1 in |- *.
unfold p in |- *.
unfold x_1 in |- *.
rewrite <- x0_ind in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
rewrite H6 in H3.
assert (cF = MF.f).
tauto.
rewrite H8 in H3.
assert (i = (p - 1)%nat).
apply (MF.unicity_mod_p m x_1).
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
generalize (exd_cA_1 m one x).
unfold x_1 in |- *.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
tauto.
fold p in Hj.
decompose [and] Hj.
assert (i = j).
omega.
rewrite H13 in H10.
rewrite H10 in H12.
tauto.
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
generalize (exd_cA_1 m one x).
unfold x_1 in |- *.
tauto.
intros.
elim H2.
clear H2.
intros.
elim H2.
clear H2.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
unfold betweenf in H2.
unfold MF.between in H2.
elim H2.
intros i Hi.
clear H2.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
set (p := MF.Iter_upb m xh0_1) in |- *.
fold p in H8.
clear Hj.
assert (x_1 = cF m x0).
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
rewrite H7 in H2.
rewrite <- H6 in H2.
assert (MF.f = cF).
tauto.
rewrite <- H9 in H2.
assert (MF.f m (Iter (MF.f m) j xh0_1) = Iter (MF.f m) (S j) xh0_1).
simpl in |- *.
tauto.
rewrite H10 in H2.
elim (eq_nat_dec (S j) p).
intro.
rewrite a0 in H2.
unfold p in H2.
rewrite MF.Iter_upb_period in H2.
assert (x_1 = xh0_1).
rewrite H7 in |- *.
rewrite <- H6 in |- *.
rewrite <- H9 in |- *.
rewrite H10 in |- *.
rewrite a0 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x).
tauto.
unfold x_1 in H11.
assert (x = xh0).
assert (cA m one x_1 = cA m one xh0_1).
fold x_1 in H11.
rewrite H11 in |- *.
tauto.
unfold x_1 in H12.
unfold xh0_1 in H12.
rewrite cA_cA_1 in H12.
rewrite cA_cA_1 in H12.
tauto.
tauto.
unfold xh0 in |- *.
apply exd_top.
tauto.
tauto.
tauto.
tauto.
unfold xh0 in H12.
absurd (succ m zero x).
rewrite H12 in |- *.
apply not_succ_top.
tauto.
tauto.
tauto.
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x).
tauto.
intro.
assert (i = S j).
apply (MF.unicity_mod_p m xh0_1 i (S j) H).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x).
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
tauto.
absurd (i = S j).
omega.
tauto.
tauto.
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x).
tauto.
clear H2.
intro.
absurd (expf m x_1 x_1).
tauto.
apply expf_refl.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
tauto.
intro.
generalize (expf_B0_CS m x x_1 x0).
simpl in |- *.
fold x_1 in |- *.
fold xb0 in |- *.
set (xh0 := top m zero x) in |- *.
set (xh0_1 := cA_1 m one xh0) in |- *.
fold x0 in |- *.
intros.
generalize (H2 H H0).
clear H2.
elim (expf_dec m x0 xb0).
tauto.
intros.
apply H2.
clear H2.
clear b.
right.
right.
apply expf_symm.
unfold x0 in |- *.
unfold x_1 in |- *.
apply expf_x0_x_1.
tauto.
apply succ_exd with zero.
tauto.
tauto.
