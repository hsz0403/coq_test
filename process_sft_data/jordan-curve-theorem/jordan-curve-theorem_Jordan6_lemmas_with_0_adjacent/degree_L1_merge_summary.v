Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem degree_L1_merge_summary: forall (m:fmap)(x y z:dart), let y0 := cA m zero y in let m1 := L m one x y in inv_hmap m1 -> exd m z -> ~expf m x y0 -> let dx:= MF.degree m x in let dy0:= MF.degree m y0 in MF.degree m1 z = if expf_dec m x z then dx + dy0 else if expf_dec m y0 z then dx + dy0 else MF.degree m z.
Proof.
intros.
elim (expf_dec m x z).
intro.
assert (expf m1 x z).
unfold m1 in |- *.
apply expf_L1_x.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
tauto.
rewrite (MF.expo_degree m1 z x) in |- *.
unfold dx in |- *.
unfold dy0 in |- *.
unfold m1 in |- *.
unfold y0 in |- *.
apply degree_L1_merge_x.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
tauto.
unfold expf in H2.
apply MF.expo_symm.
tauto.
tauto.
elim (expf_dec m y0 z).
intros.
assert (expf m1 y0 z).
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_y0.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite (MF.expo_degree m1 z y0) in |- *.
unfold dx in |- *.
unfold dy0 in |- *.
unfold m1 in |- *.
unfold y0 in |- *.
apply degree_L1_merge_y0.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
tauto.
apply MF.expo_symm.
tauto.
unfold expf in H2.
tauto.
intros.
unfold m1 in |- *.
apply degree_L1_merge_x_others.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
