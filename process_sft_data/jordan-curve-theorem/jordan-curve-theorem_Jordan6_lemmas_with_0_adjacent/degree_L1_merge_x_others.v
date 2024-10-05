Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem degree_L1_merge_x_others: forall(m:fmap)(x y z:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> exd m z -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> MF.degree m1 z = MF.degree m z.
Proof.
intros.
unfold MF.degree in |- *.
unfold m1 in |- *.
generalize (MF.degree_lub m z).
simpl in |- *.
set (dz := MF.degree m z) in |- *.
intro.
assert (0 < dz).
unfold m1 in H.
simpl in H.
tauto.
assert (1 = dz - (dz - 1)).
omega.
rewrite H6 in |- *.
unfold dz in |- *.
apply degree_L1_merge_x_others_aux.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold dz in |- *.
omega.
