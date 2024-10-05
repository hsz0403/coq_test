Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1_x10:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx := MF.degree m x in ~expf m x y0 -> Iter (cF m1) dx x = y_1.
Proof.
intros.
unfold prec_L in H0.
assert (exd m x).
tauto.
generalize (MF.degree_lub m x H H2).
simpl in |- *.
fold dx in |- *.
intros.
decompose [and] H3.
clear H3.
set (x10 := cF_1 m x) in |- *.
assert (x10 = Iter (cF m) (dx - 1) x).
unfold x10 in |- *.
assert (MF.Iter_upb m x = dx).
unfold dx in |- *.
apply MF.upb_eq_degree.
tauto.
tauto.
assert (cF_1 = MF.f_1).
tauto.
assert (cF = MF.f).
tauto.
rewrite H5 in |- *.
rewrite H8 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite H6 in |- *.
tauto.
tauto.
tauto.
omega.
assert (dx = S (dx - 1)).
omega.
rewrite H5 in |- *.
simpl in |- *.
unfold m1 in |- *.
rewrite cF_L1_x_x10 in |- *.
rewrite <- H3 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
fold x10 in |- *.
fold y_1 in |- *.
elim (eq_dart_dec y0 x10).
unfold x10 in |- *.
intro.
elim H1.
rewrite a in |- *.
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_cF_1 m x).
tauto.
split with 1.
simpl in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H8 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec x10 x10).
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
