Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma diff_x_x10:forall(m:fmap)(x y:dart)(i:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let dx := MF.degree m x in let m1:= L m one x y in ~expf m x y0 -> 0 < i <= dx - 1 -> Iter (cF m1) i x <> x.
Proof.
intros.
generalize (cF_L1_x_x10 m x y i H H0).
simpl in |- *.
fold y0 in |- *; fold dx in |- *.
fold m1 in |- *.
intros.
generalize (H3 H1).
clear H3.
intro.
rewrite H3 in |- *.
unfold prec_L in H0.
assert (exd m x).
tauto.
generalize (MF.degree_lub m x H H4).
simpl in |- *.
fold dx in |- *.
intros.
decompose [and] H5.
clear H5.
apply H9.
split.
omega.
omega.
omega.
