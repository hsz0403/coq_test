Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem degree_L1_split_x_y_1: forall(m:fmap)(x y:dart)(j:nat), let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx:= MF.degree m x in y_1 = Iter (cF m) j x -> inv_hmap m1 -> 1 <= j <= dx -1 -> expf m x y0 -> MF.degree m1 x = j.
Proof.
intros.
assert (j = S (j - 1)).
omega.
assert (y0 = Iter (cF m) (j - 1) x).
rewrite H3 in H.
simpl in H.
assert (Iter (cF m) (j - 1) x = cF_1 m y_1).
rewrite H in |- *.
rewrite cF_1_cF in |- *.
tauto.
unfold m1 in H0.
simpl in H0.
tauto.
generalize (MF.exd_Iter_f m (j - 1) x).
unfold m1 in H0.
simpl in H0.
unfold prec_L in H0.
tauto.
unfold y_1 in H4.
unfold cF_1 in H4.
rewrite cA_cA_1 in H4.
fold y0 in H4.
symmetry in |- *.
tauto.
unfold m1 in H0.
simpl in H0.
unfold prec_L in H0.
tauto.
unfold m1 in H0.
simpl in H0.
unfold prec_L in H0.
tauto.
unfold m1 in |- *.
rewrite (degree_L1_split_x_y0 m x y (j - 1)) in |- *.
omega.
fold y0 in |- *.
tauto.
fold m1 in |- *.
tauto.
fold dx in |- *.
omega.
fold y0 in |- *.
tauto.
