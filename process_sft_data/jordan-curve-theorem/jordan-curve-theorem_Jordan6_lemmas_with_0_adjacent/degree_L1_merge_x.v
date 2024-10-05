Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem degree_L1_merge_x: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> ~expf m x y0 -> MF.degree m1 x = MF.degree m x + MF.degree m y0.
Proof.
intros.
set (dx := MF.degree m x) in |- *.
set (dy0 := MF.degree m y0) in |- *.
fold y0 in |- *.
set (MAX := dx + dy0) in |- *.
generalize (degree_L1_merge_aux m x y (MAX - 1) H H0).
fold y0 in |- *.
fold m1 in |- *.
fold dx in |- *.
fold dy0 in |- *.
fold MAX in |- *.
intros.
simpl in H.
unfold prec_L in H.
decompose [and] H.
clear H.
generalize (MF.degree_lub m x H2 H4).
simpl in |- *.
fold dx in |- *.
intros.
assert (0 < MAX).
unfold MAX in |- *.
omega.
assert (MAX - (MAX - 1) = 1).
omega.
rewrite H9 in H1.
unfold MF.degree in |- *.
apply H1.
omega.
