Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem orb_x_eqs_orb_y0: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> eqs (MF.Iter_orb m1 x) (MF.Iter_orb m1 y0).
Proof.
intros.
apply MF.eqs_orb.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
unfold y0 in |- *.
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
fold y0 in |- *.
elim (eq_dart_dec y0 y0).
tauto.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H.
tauto.
