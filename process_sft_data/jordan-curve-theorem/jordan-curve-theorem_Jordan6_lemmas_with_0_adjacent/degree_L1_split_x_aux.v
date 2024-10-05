Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma degree_L1_split_x_aux: forall(m:fmap)(x y:dart)(j i:nat), let m1:= L m one x y in let y0 := cA m zero y in let dx:= MF.degree m x in y0 = Iter (cF m) j x -> i < j < dx - 1 -> expf m x y0 -> inv_hmap m1 -> MF.degree_aux m1 x (j - i) = j + 1.
Proof.
intros.
assert (inv_hmap m1).
tauto.
unfold m1 in H2.
simpl in H2.
unfold prec_L in H2.
decompose [and] H2.
clear H2.
generalize (MF.degree_bound m x H4 H6).
fold dx in |- *.
intro.
assert (cF = MF.f).
tauto.
intros.
induction i.
assert (j - 0 = j).
omega.
rewrite H11 in |- *.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
simpl in |- *.
fold m1 in |- *.
clear H11.
elim (le_lt_dec j (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f m1) j x)).
intro.
symmetry in a0.
absurd (Iter (MF.f m1) j x = x).
unfold m1 in |- *.
rewrite <- H9 in |- *.
rewrite (cF_L1_x_y0 m x y j j) in |- *.
apply (MF.degree_diff m x H4 H6).
fold dx in |- *.
omega.
tauto.
unfold prec_L in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
tauto.
elim (eq_nat_dec j (ndN m)).
intros.
omega.
intros.
unfold m1 in |- *.
rewrite MF.degree_aux_equation in |- *.
simpl in |- *.
fold m1 in |- *.
elim (le_lt_dec (j + 1) (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f m1) (j + 1) x)).
tauto.
intro.
elim b1.
assert (S j = j + 1).
omega.
rewrite <- H11 in |- *.
simpl in |- *.
unfold m1 in |- *.
rewrite <- H9 in |- *.
rewrite (cF_L1_x_y0 m x y j j) in |- *.
rewrite <- H in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 y0).
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
intro.
omega.
intro.
omega.
unfold m1 in |- *.
rewrite MF.degree_aux_equation in |- *.
simpl in |- *.
fold m1 in |- *.
elim (le_lt_dec (j - S i) (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f m1) (j - S i) x)).
intro.
symmetry in a0.
absurd (Iter (MF.f m1) (j - S i) x = x).
unfold m1 in |- *.
rewrite <- H9 in |- *.
apply (diff_cF_L1_x_y0 m x y (j - S i) j).
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
split.
omega.
omega.
tauto.
intro.
elim (eq_nat_dec (j - S i) (ndN m)).
intro.
omega.
intro.
assert (j - S i + 1 = j - i).
omega.
rewrite H11 in |- *.
apply IHi.
omega.
intros.
omega.
