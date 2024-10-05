Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem degree_L1_merge_y0: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> ~expf m x y0 -> MF.degree m1 y0 = MF.degree m x + MF.degree m y0.
Proof.
intros.
assert (expf m1 y0 x).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
unfold m1 in |- *.
simpl in |- *.
generalize (exd_cA m zero y).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H1 in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) y0).
tauto.
fold y0 in |- *.
tauto.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
rewrite (MF.expo_degree m1 y0 x H) in |- *.
unfold y0 in |- *.
unfold m1 in |- *.
apply degree_L1_merge_x.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
unfold expf in H1.
tauto.
