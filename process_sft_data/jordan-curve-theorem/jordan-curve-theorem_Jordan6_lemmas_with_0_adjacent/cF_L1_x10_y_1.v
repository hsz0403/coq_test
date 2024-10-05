Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1_x10_y_1:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> j < dx - 1 -> Iter (cF m1) (dx - (j + 1)) y_1 = y_1.
Proof.
intros.
assert (dx - (j + 1) = S (dx - (j + 2))).
omega.
rewrite H4 in |- *.
clear H4.
simpl in |- *.
unfold m1 in |- *.
unfold y_1 in |- *.
rewrite (cF_L1_y_1_x10 m x y (dx - (j + 2)) j) in |- *.
assert (j + 1 + (dx - (j + 2)) = dx - 1).
omega.
rewrite H4 in |- *.
clear H4.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold dx in |- *.
rewrite MF.degree_per in |- *.
assert (MF.f_1 = cF_1).
tauto.
assert (exd m (cF_1 m x)).
generalize (exd_cF_1 m x).
unfold prec_L in H0.
tauto.
rewrite H4 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) (cF_1 m x)).
intro.
assert (y = cA_1 m zero (cF_1 m x)).
rewrite <- a in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
unfold cF_1 in H6.
rewrite cA_1_cA in H6.
symmetry in H6.
unfold prec_L in H0.
tauto.
tauto.
generalize (exd_cA m one x).
unfold prec_L in H0.
tauto.
intro.
elim (eq_dart_dec (cF_1 m x) (cF_1 m x)).
fold y_1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold prec_L in H0.
tauto.
tauto.
unfold prec_L in H0.
tauto.
omega.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
omega.
