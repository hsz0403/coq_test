Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma diff_y_1_y0_aux:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx := MF.degree m x in let dy_1 := MF.degree m y_1 in ~expf m x y0 -> j <= dy_1 -1 -> Iter (cF m1) (dx + j) x <> x.
Proof.
intros.
generalize (cF_L1_y_1_y0_aux m x y j H H0 H1).
fold y0 in |- *.
fold y_1 in |- *.
fold m1 in |- *.
fold dx in |- *.
fold dy_1 in |- *.
intros.
generalize (H3 H2).
intro.
clear H3.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m y_1 H H3).
simpl in |- *.
fold dy_1 in |- *.
intros.
decompose [and] H5.
clear H5.
rewrite H4 in |- *.
intro.
assert (y = cA_1 m zero y0).
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (y_1 = cF m y0).
unfold y_1 in |- *.
rewrite H7 in |- *.
fold (cF m y0) in |- *.
tauto.
assert (expf m y0 y_1).
rewrite H10 in |- *.
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
assert (expf m y_1 (Iter (cF m) j y_1)).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with j.
tauto.
elim H1.
apply expf_trans with y_1.
rewrite <- H5 in |- *.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
