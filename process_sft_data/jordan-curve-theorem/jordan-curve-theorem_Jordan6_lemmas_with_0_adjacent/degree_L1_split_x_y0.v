Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem degree_L1_split_x_y0: forall(m:fmap)(x y:dart)(j:nat), let m1:= L m one x y in let y0 := cA m zero y in let dx:= MF.degree m x in y0 = Iter (cF m) j x -> inv_hmap m1 -> j < dx -1 -> expf m x y0 -> MF.degree m1 x = j + 1.
Proof.
intros.
assert (inv_hmap m1).
tauto.
intros.
assert (inv_hmap m1).
tauto.
unfold m1 in H3.
simpl in H3.
unfold prec_L in H3.
decompose [and] H3.
clear H3.
generalize (MF.degree_bound m x H5 H7).
generalize (MF.degree_pos m x H7).
fold dx in |- *.
intros.
unfold MF.degree in |- *.
elim (eq_nat_dec j 0).
intro.
rewrite a in |- *.
simpl in H.
simpl in |- *.
rewrite MF.degree_aux_equation in |- *.
elim (le_lt_dec 1 (ndN m1)).
intro.
unfold m1 in a0.
simpl in a0.
elim (eq_dart_dec x (Iter (MF.f m1) 1 x)).
tauto.
intro.
elim b.
simpl in |- *.
unfold m1 in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H12 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 x).
tauto.
rewrite a in H.
simpl in H.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
unfold m1 in |- *.
simpl in |- *.
intro.
omega.
intro.
unfold MF.degree in |- *.
assert (1 = j - (j - 1)).
omega.
rewrite H12 in |- *.
unfold m1 in |- *.
rewrite degree_L1_split_x_aux in |- *.
omega.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
fold y0 in |- *.
tauto.
fold m1 in |- *.
tauto.
