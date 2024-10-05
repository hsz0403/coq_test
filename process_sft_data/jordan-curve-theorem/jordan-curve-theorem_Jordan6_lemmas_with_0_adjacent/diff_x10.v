Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma diff_x10:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let dx := MF.degree m x in ~expf m x y0 -> Iter (cF m1) dx x <> x.
Proof.
intros.
unfold dx in |- *.
unfold m1 in |- *.
rewrite cF_L1_x10 in |- *.
intro.
apply H1.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
assert (cA_1 m one y = cF m y0).
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
rewrite <- H2 in |- *.
rewrite H3 in |- *.
split with 1.
simpl in |- *.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
