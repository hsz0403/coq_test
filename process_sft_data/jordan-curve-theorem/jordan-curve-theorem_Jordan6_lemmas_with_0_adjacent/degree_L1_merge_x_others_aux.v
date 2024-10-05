Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma degree_L1_merge_x_others_aux: forall(m:fmap)(x y z:dart)(n:nat), let m1:= L m one x y in let y0 := cA m zero y in let dz:= MF.degree m z in inv_hmap m1 -> exd m z -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> n < dz -> MF.degree_aux m1 z (dz - n) = MF.degree_aux m z (dz - n).
Proof.
induction n.
intros.
rename H4 into dzp.
assert (dz - 0 = dz).
omega.
rewrite H4 in |- *.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
rewrite ndN_L in |- *.
fold m1 in |- *.
rewrite (MF.degree_aux_equation m z dz) in |- *.
elim (le_lt_dec dz (ndN m)).
elim (eq_dart_dec z (Iter (MF.f m1) dz z)).
intros.
unfold m1 in a.
elim (eq_dart_dec z (Iter (MF.f m) dz z)).
tauto.
intro.
assert (MF.f = cF).
tauto.
rewrite H5 in a.
rewrite H5 in b.
rewrite Iter_cF_L1_i in a.
tauto.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
intro.
generalize (MF.degree_lub m z).
simpl in |- *.
fold dz in |- *.
intro.
elim b.
symmetry in |- *.
unfold m1 in H.
simpl in H.
unfold m1 in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H6 in |- *.
rewrite <- H6 in H5.
rewrite Iter_cF_L1_i in |- *.
tauto.
simpl in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
intros.
rename H4 into dzp.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
rewrite ndN_L in |- *.
rewrite (MF.degree_aux_equation m z (dz - S n)) in |- *.
elim (le_lt_dec (dz - S n) (ndN m)).
assert (MF.f = cF).
tauto.
rewrite H4 in |- *.
rewrite Iter_cF_L1_i in |- *.
elim (eq_dart_dec z (Iter (cF m) (dz - S n) z)).
tauto.
intros.
elim (eq_nat_dec (dz - S n) (ndN m)).
tauto.
intros.
assert (dz - S n + 1 = dz - n).
assert (dz <> S n).
intro.
rewrite H5 in b.
simpl in b.
assert (n - n = 0).
omega.
rewrite H6 in b.
simpl in b.
tauto.
generalize (MF.degree_lub m z).
simpl in |- *.
fold dz in |- *.
unfold m1 in H.
intro.
assert (0 < dz).
simpl in H.
tauto.
omega.
rewrite H5 in |- *.
unfold dz in |- *.
apply IHn.
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
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
