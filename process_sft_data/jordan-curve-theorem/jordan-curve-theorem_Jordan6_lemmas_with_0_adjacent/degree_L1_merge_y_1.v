Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem degree_L1_merge_y_1: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y_1 := cA_1 m one y in inv_hmap m1 -> ~expf m x y_1 -> MF.degree m1 x = MF.degree m x + MF.degree m y_1.
Proof.
intros.
set (y0 := cA m zero y) in |- *.
assert (~ expf m x y0).
intro.
unfold m1 in H.
simpl in H.
decompose [and] H.
clear H.
generalize (expf_y0_y_1 m x y H2 H3).
simpl in |- *.
fold y0 in |- *.
fold y_1 in |- *.
intro.
elim H0.
apply expf_trans with y0.
tauto.
tauto.
unfold y_1 in |- *.
rewrite <- (degree_y0_y_1 m x y) in |- *.
unfold m1 in |- *.
apply degree_L1_merge_x.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
unfold m1 in |- *.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
