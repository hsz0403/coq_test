Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma diff_cF_L1_y_1_y_1:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> j + 1 + i <= dx - 1 -> 0 < i -> Iter (cF m1) i y_1 <> y_1.
Proof.
intros.
unfold m1 in |- *.
unfold y_1 in |- *.
rewrite (cF_L1_y_1_x10 m x y i j) in |- *.
fold y_1 in |- *.
assert (y_1 = Iter (cF m) 1 y0).
simpl in |- *.
unfold y0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
rewrite H5 in |- *.
rewrite H1 in |- *.
rewrite <- MF.Iter_comp in |- *.
intro.
assert (j + 1 + i = 1 + j).
apply (MF.degree_unicity m x).
tauto.
unfold prec_L in H0.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
omega.
tauto.
absurd (j + 1 + i = 1 + j).
omega.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
fold dx in |- *.
omega.
fold dx in |- *.
tauto.
