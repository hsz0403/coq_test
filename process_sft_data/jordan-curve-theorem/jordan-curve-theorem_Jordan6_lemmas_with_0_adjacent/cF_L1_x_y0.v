Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1_x_y0:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> (i <= j < dx - 1) -> Iter (cF m1) i x = Iter (cF m) i x.
Proof.
intros.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
assert (cF = MF.f).
tauto.
rewrite H4 in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite H5 in |- *.
elim (eq_dart_dec y0 (Iter (MF.f m) i x)).
intro.
rewrite H4 in H1.
rewrite H1 in a.
assert (j = i).
apply (MF.degree_unicity m x j i).
tauto.
unfold prec_L in H0.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
omega.
tauto.
absurd (j = i).
omega.
tauto.
elim (eq_dart_dec (MF.f_1 m x) (Iter (MF.f m) i x)).
intros.
assert (x = MF.f m (Iter (MF.f m) i x)).
rewrite <- a in |- *.
rewrite <- H4 in |- *.
rewrite <- H5 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (x = Iter (MF.f m) (S i) x).
simpl in |- *.
tauto.
assert (exd m x).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m x H H8).
simpl in |- *.
fold dx in |- *.
intros.
decompose [and] H9.
symmetry in H7.
absurd (Iter (MF.f m) (S i) x = x).
apply H13.
omega.
tauto.
tauto.
tauto.
tauto.
omega.
