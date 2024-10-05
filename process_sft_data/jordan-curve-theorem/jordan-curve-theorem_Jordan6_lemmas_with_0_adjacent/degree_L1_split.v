Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem degree_L1_split: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in let y_1:= cA_1 m one y in inv_hmap (L m one x y) -> expf m x y0 -> MF.degree m x = MF.degree m1 x + MF.degree m1 y_1.
Proof.
intros.
assert (MF.expo1 m x y0).
unfold expf in H0.
assert (exd m x).
unfold MF.expo in H0.
tauto.
generalize (MF.expo_expo1 m x y0).
tauto.
unfold MF.expo1 in H1.
decompose [and] H1.
clear H1.
elim H3.
intros j Hj.
clear H3.
elim Hj.
clear Hj.
intros.
set (dx := MF.Iter_upb m x) in |- *.
fold dx in H1.
assert (dx = MF.degree m x).
unfold dx in |- *.
apply MF.upb_eq_degree.
simpl in H.
tauto.
tauto.
assert (0 < dx).
unfold dx in |- *.
apply MF.upb_pos.
tauto.
assert (j <> dx - 1).
intro.
rewrite H6 in H3.
rewrite <- MF.Iter_f_f_1 in H3.
simpl in H3.
unfold dx in H3.
rewrite MF.Iter_upb_period in H3.
assert (MF.f_1 = cF_1).
tauto.
rewrite H7 in H3.
unfold cF_1 in H3.
unfold y0 in H3.
assert (cA_1 m zero (cA m zero (cA m one x)) = y).
rewrite H3 in |- *.
rewrite cA_1_cA in |- *.
tauto.
simpl in H.
tauto.
simpl in H; unfold prec_L in H.
tauto.
rewrite cA_1_cA in H8.
simpl in H.
unfold prec_L in H.
tauto.
simpl in H; unfold prec_L in H.
tauto.
generalize (exd_cA m one x).
simpl in H; unfold prec_L in H.
tauto.
simpl in H; unfold prec_L in H.
tauto.
tauto.
simpl in H; unfold prec_L in H.
tauto.
tauto.
omega.
unfold m1 in |- *.
unfold y_1 in |- *.
rewrite (degree_L1_split_x_y0 m x y j) in |- *.
rewrite (degree_L1_split_y_1 m x y j) in |- *.
omega.
fold y0 in |- *.
symmetry in |- *.
tauto.
rewrite <- H4 in |- *.
omega.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
tauto.
rewrite <- H4 in |- *.
omega.
fold y0 in |- *.
tauto.
