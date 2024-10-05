Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1_y0:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let dx := MF.degree m x in let dy0 := MF.degree m y0 in ~expf m x y0 -> Iter (cF m1) (dx + dy0) x = x.
Proof.
intros.
assert (cF = MF.f).
tauto.
set (y_1 := cA_1 m one y) in |- *.
set (dy_1 := MF.degree m y_1) in |- *.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
unfold prec_L in H0.
tauto.
assert (y = cA_1 m zero y0).
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (y_1 = cF m y0).
unfold y_1 in |- *.
rewrite H4 in |- *.
fold (cF m y0) in |- *.
tauto.
assert (expf m y0 y_1).
rewrite H5 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
split with 1.
simpl in |- *.
tauto.
assert (MF.degree m y0 = MF.degree m y_1).
symmetry in |- *.
apply MF.expo_degree.
tauto.
unfold expf in H6.
apply MF.expo_symm.
tauto.
tauto.
fold dy0 in H7.
fold dy_1 in H7.
rewrite H7 in |- *.
generalize (MF.degree_lub m y_1 H H3).
simpl in |- *.
fold dy_1 in |- *.
intro.
decompose [and] H8.
clear H8.
assert (dx + dy_1 = S (dx + (dy_1 - 1))).
omega.
rewrite H8 in |- *.
simpl in |- *.
unfold dx in |- *.
unfold m1 in |- *.
rewrite cF_L1_y_1_y0 in |- *.
fold y_1 in |- *.
assert (y0 = Iter (cF m) (dy_1 - 1) y_1).
rewrite H5 in |- *.
rewrite <- H7 in |- *.
assert (cF m y0 = Iter (MF.f m) 1 y0).
simpl in |- *.
tauto.
rewrite H10 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (dy0 - 1 + 1 = dy0).
omega.
rewrite H13 in |- *.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m y0 H H14).
simpl in |- *.
fold dy0 in |- *.
intros.
symmetry in |- *.
tauto.
rewrite <- H10 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) y0).
fold y0 in |- *.
tauto.
elim (eq_dart_dec (cF_1 m x) y0).
intros.
elim H1.
rewrite <- a in |- *.
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_cF_1 m x).
unfold prec_L in H0.
tauto.
split with 1.
simpl in |- *.
tauto.
fold y0 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y_1 in |- *.
fold dy_1 in |- *.
fold y0 in |- *.
fold dy0 in |- *.
rewrite H7 in |- *.
omega.
