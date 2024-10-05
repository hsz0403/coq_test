Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma Iter_cF_L1_i: forall(m:fmap)(x y z:dart)(i:nat), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> exd m z -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> Iter (cF m1) i z = Iter (cF m) i z.
Proof.
intros.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
set (zi := Iter (cF m) i z) in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
set (y_1 := cA_1 m one y) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H4.
simpl in H4.
unfold prec_L in H4.
decompose [and] H4.
assert (expf m z zi).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
tauto.
elim (eq_dart_dec y0 zi).
intro.
rewrite <- a in H10.
elim H3.
apply expf_symm.
tauto.
elim (eq_dart_dec (cF_1 m x) zi).
intros.
rewrite <- a in H10.
elim H2.
apply expf_trans with (cF_1 m x).
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_cF_1 m x).
tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H12 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
apply expf_symm.
tauto.
tauto.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
