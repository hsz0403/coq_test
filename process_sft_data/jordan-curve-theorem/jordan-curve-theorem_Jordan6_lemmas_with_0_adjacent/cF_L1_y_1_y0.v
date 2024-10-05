Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1_y_1_y0:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx := MF.degree m x in let dy0 := MF.degree m y0 in ~expf m x y0 -> j <= dy0 -1 -> Iter (cF m1) (dx + j) x = Iter (cF m) j y_1.
Proof.
intros.
set (dy_1 := MF.degree m y_1) in |- *.
assert (y = cA_1 m zero y0).
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (y_1 = cF m y0).
unfold y_1 in |- *.
rewrite H3 in |- *.
fold (cF m y0) in |- *.
tauto.
assert (expf m y0 y_1).
rewrite H4 in |- *.
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
unfold expf in H5.
apply MF.expo_symm.
tauto.
tauto.
fold dy0 in H6.
fold dy_1 in H6.
unfold m1 in |- *.
unfold y_1 in |- *.
unfold dx in |- *.
apply cF_L1_y_1_y0_aux.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y_1 in |- *.
fold dy_1 in |- *.
rewrite <- H6 in |- *.
tauto.
