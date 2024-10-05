Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma not_expf_L1_y0: forall(m:fmap)(x y z:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> ~expf m1 y0 z.
Proof.
intros.
intro.
assert (expf m1 x y0).
unfold m1 in |- *.
unfold y0 in |- *.
apply (expf_L1_x_y0 m x y H).
fold y0 in |- *.
tauto.
generalize (not_expf_L1_x m x y z H H0 H1 H2).
fold m1 in |- *.
intro.
elim H5.
apply expf_trans with y0.
tauto.
tauto.
