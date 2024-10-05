Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma expf_L1_y0: forall (m:fmap)(x y z:dart), let y0 := cA m zero y in let m1 := L m one x y in inv_hmap m1 -> ~expf m x y0 -> expf m y0 z -> expf m1 y0 z.
Proof.
intros.
set (y_1 := cA_1 m one y) in |- *.
assert (expf m y_1 z).
apply expf_trans with y0.
apply expf_symm.
unfold expf in |- *.
split.
unfold m1 in H; simpl in H.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
split with 1.
simpl in |- *.
unfold y_1 in |- *.
unfold y0 in |- *.
unfold MF.f in |- *.
unfold McF.f in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
tauto.
apply expf_trans with x.
apply expf_symm.
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_x_y0.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
unfold expf in |- *.
unfold expf in H2.
assert (MF.expo1 m y_1 z).
generalize (MF.expo_expo1 m y_1 z).
intro.
assert (MF.expo1 m y_1 z).
tauto.
tauto.
unfold MF.expo1 in H3.
decompose [and] H3.
clear H3.
elim H5.
clear H5.
intros j Hj.
set (dy_1 := MF.Iter_upb m y_1) in |- *.
fold dy_1 in Hj.
decompose [and] Hj.
clear Hj.
split.
unfold m1 in |- *.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
set (dx := MF.degree m x) in |- *.
unfold y_1 in dy_1.
split with (dx + j).
assert (MF.f = cF).
tauto.
rewrite H6 in |- *.
unfold m1 in |- *.
unfold dx in |- *.
rewrite cF_L1_y_1_y0_aux in |- *.
fold y_1 in |- *.
rewrite <- H6 in |- *.
tauto.
unfold m1 in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
fold y0 in |- *.
tauto.
rewrite <- MF.upb_eq_degree in |- *.
fold dy_1 in |- *.
omega.
unfold m1 in |- *.
tauto.
generalize (exd_cA_1 m one y).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
