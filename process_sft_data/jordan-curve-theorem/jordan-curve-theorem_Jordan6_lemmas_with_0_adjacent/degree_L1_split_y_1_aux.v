Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma degree_L1_split_y_1_aux: forall(m:fmap)(x y:dart)(j i:nat), let m1:= L m one x y in let y0 := cA m zero y in let y_1:= cA_1 m one y in let dx:= MF.degree m x in y0 = Iter (cF m) j x -> j + 1 + i < dx -> expf m x y0 -> inv_hmap m1 -> MF.degree_aux m1 y_1 (dx - (j + 1 + i)) = dx - (j + 1).
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
induction i.
assert (j + 1 + 0 = j + 1).
omega.
rewrite H11 in |- *.
clear H11.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
simpl in |- *.
fold m1 in |- *.
elim (le_lt_dec (dx - (j + 1)) (ndN m)).
intro.
elim (eq_dart_dec y_1 (Iter (MF.f m1) (dx - (j + 1)) y_1)).
tauto.
intro.
elim b.
symmetry in |- *.
rewrite <- H9 in |- *.
assert (dx - (j + 1) = S (dx - j - 2)).
omega.
rewrite H11 in |- *.
simpl in |- *.
unfold y_1 in |- *.
unfold m1 in |- *.
rewrite (cF_L1_y_1_x10 m x y (dx - j - 2) j) in |- *.
assert (j + 1 + (dx - j - 2) = dx - 1).
clear H11.
omega.
rewrite H12 in |- *.
rewrite H9 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold dx in |- *.
rewrite MF.degree_per in |- *.
rewrite <- H9 in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H13 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) (cF_1 m x)).
intro.
unfold cF_1 in a0.
assert (y = cA_1 m zero (cA m zero (cA m one x))).
rewrite <- a0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite cA_1_cA in H14.
rewrite H14 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
tauto.
generalize (exd_cA m one x).
tauto.
elim (eq_dart_dec (cF_1 m x) (cF_1 m x)).
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H12.
clear H11.
omega.
clear H11.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
clear H11.
omega.
fold dx in |- *.
clear H11.
omega.
intro.
omega.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
simpl in |- *.
fold m1 in |- *.
elim (le_lt_dec (dx - (j + 1 + S i)) (ndN m)).
intro.
elim (eq_dart_dec y_1 (Iter (MF.f m1) (dx - (j + 1 + S i)) y_1)).
intro.
symmetry in a0.
absurd (Iter (MF.f m1) (dx - (j + 1 + S i)) y_1 = y_1).
unfold m1 in |- *.
unfold y_1 in |- *.
apply (diff_cF_L1_y_1_y_1 m x y (dx - (j + 1 + S i)) j).
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
omega.
tauto.
elim (eq_nat_dec (dx - (j + 1 + S i)) (ndN m)).
intro.
intro.
omega.
intros.
assert (dx - (j + 1 + S i) + 1 = dx - (j + 1 + i)).
omega.
rewrite H11 in |- *.
apply IHi.
clear H11.
omega.
intro.
omega.
