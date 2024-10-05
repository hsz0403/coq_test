Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1_y_1_x10:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> j < dx - 1 -> j + 1 + i <= dx - 1 -> Iter (cF m1) i y_1 = Iter (cF m) (j + 1 + i) x.
intros.
intros.
induction i.
simpl in |- *.
assert (j + 1 + 0 = S j).
omega.
rewrite H5 in |- *.
simpl in |- *.
rewrite <- H1 in |- *.
unfold y0 in |- *.
unfold y_1 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (j + 1 + S i = S (j + 1 + i)).
omega.
rewrite H5 in |- *.
simpl in |- *.
clear H5.
rewrite IHi in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 (Iter (cF m) (j + 1 + i) x)).
intros.
rewrite H1 in a.
assert (j = j + 1 + i).
assert (exd m x).
unfold prec_L in H0.
tauto.
apply (MF.degree_unicity m x).
tauto.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
omega.
tauto.
absurd (j = j + 1 + i).
omega.
tauto.
elim (eq_dart_dec (cF_1 m x) (Iter (cF m) (j + 1 + i) x)).
intros.
assert (x = Iter (cF m) (S (j + 1 + i)) x).
simpl in |- *.
rewrite <- a in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
symmetry in H5.
absurd (Iter (cF m) (S (j + 1 + i)) x = x).
apply MF.degree_diff.
tauto.
unfold prec_L in H0.
tauto.
fold dx in |- *.
omega.
tauto.
tauto.
tauto.
tauto.
omega.
