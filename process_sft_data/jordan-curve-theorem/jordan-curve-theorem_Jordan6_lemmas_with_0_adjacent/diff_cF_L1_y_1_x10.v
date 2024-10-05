Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma diff_cF_L1_y_1_x10:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> j + 1 + i <= dx - 1 -> Iter (cF m1) i y_1 <> x.
Proof.
intros.
unfold m1 in |- *.
unfold y_1 in |- *.
rewrite (cF_L1_y_1_x10 m x y i j H H0) in |- *.
assert (exd m x).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m x H H4).
simpl in |- *.
fold dx in |- *.
intro.
decompose [and] H5.
clear H5.
apply H9.
omega.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
omega.
