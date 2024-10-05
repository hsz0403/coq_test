Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma expf_L1_x_y0: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> ~expf m x y0 -> expf m1 x y0.
Proof.
intros.
apply expf_symm.
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
