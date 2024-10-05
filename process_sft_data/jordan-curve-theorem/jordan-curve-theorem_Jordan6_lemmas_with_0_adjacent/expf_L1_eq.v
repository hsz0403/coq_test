Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem expf_L1_eq:forall(m:fmap)(x y z t:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> (expf m1 z t <-> expf m z t).
Proof.
intros.
split.
unfold m1 in |- *.
unfold expf in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H3.
clear H3.
unfold MF.expo in H5.
decompose [and] H5.
clear H5.
simpl in H3.
elim H10.
intros i Hi.
clear H10.
assert (MF.f = cF).
tauto.
unfold MF.expo in |- *.
split.
tauto.
split.
tauto.
split with i.
rewrite H5 in |- *.
rewrite H5 in Hi.
rewrite <- (Iter_cF_L1_i m x y z i) in |- *.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
unfold expf in |- *.
simpl in |- *.
intros.
split.
unfold m1 in H.
simpl in H.
tauto.
unfold MF.expo in H3.
decompose [and] H3.
clear H3.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
elim H7.
intros i Hi.
split with i.
assert (MF.f = cF).
tauto.
rewrite H3 in |- *.
rewrite H3 in Hi.
unfold m1 in |- *.
rewrite (Iter_cF_L1_i m x y z i) in |- *.
tauto.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
