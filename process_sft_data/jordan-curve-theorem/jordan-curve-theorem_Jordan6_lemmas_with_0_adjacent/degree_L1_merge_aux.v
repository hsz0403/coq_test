Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma degree_L1_merge_aux: forall(m:fmap)(x y:dart)(n:nat), let m1:= L m one x y in let y0 := cA m zero y in let MAX:= MF.degree m x + MF.degree m y0 in inv_hmap m1 -> ~expf m x y0 -> 1 <= MAX - n -> MF.degree_aux m1 x (MAX - n) = MF.degree m x + MF.degree m y0.
Proof.
induction n.
intros.
assert (MAX - 0 = MAX).
omega.
rewrite H2 in |- *.
unfold MAX in |- *.
unfold y0 in |- *.
unfold m1 in |- *.
apply degree_L1_merge_MAX.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
intros.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
simpl in |- *.
elim (le_lt_dec (MAX - S n) (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f (L m one x y)) (MAX - S n) x)).
intros.
fold m1 in a0.
set (i := MAX - S n) in |- *.
fold i in a0.
assert (cF = MF.f).
tauto.
rewrite <- H2 in a0.
symmetry in a0.
fold i in H1.
fold i in a.
set (dx := MF.degree m x) in |- *.
fold dx in MAX.
set (dy0 := MF.degree m y0) in |- *.
fold dy0 in MAX.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
assert (inv_hmap m).
tauto.
generalize (MF.degree_lub m x H6 H3).
simpl in |- *.
fold dx in |- *.
rewrite <- H2 in |- *.
intros.
generalize (MF.degree_lub m y0 H6 H5).
simpl in |- *.
fold dy0 in |- *.
intros.
rewrite <- H2 in H8.
elim (le_lt_dec i (dx - 1)).
intro.
absurd (Iter (cF m1) i x = x).
unfold m1 in |- *.
apply (diff_x_x10 m x y).
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
tauto.
tauto.
intro.
elim (le_lt_dec i (dx + (dy0 - 1))).
intros.
absurd (Iter (cF m1) i x = x).
unfold m1 in |- *.
set (j := i - dx) in |- *.
assert (i = dx + j).
unfold j in |- *.
omega.
rewrite H9 in |- *.
apply (diff_y_1_y0 m x y j H6).
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
fold dy0 in |- *.
omega.
tauto.
intro.
unfold MAX in i.
unfold i in b0.
omega.
intros.
elim (eq_nat_dec (MAX - S n) (ndN m)).
intro.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
decompose [and] H; clear H.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
assert (~ MF.expo m x y0).
unfold expf in H0.
tauto.
generalize (MF.degree_sum_bound m x y0 H2 H4 H H7).
intro.
unfold MAX in a.
unfold MAX in a0.
generalize (MF.ndN_pos m x H4).
intro.
omega.
intro.
assert (MAX - S n + 1 = MAX - n).
omega.
rewrite H2 in |- *.
unfold MAX in |- *.
apply IHn.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
fold MAX in |- *.
omega.
intro.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
decompose [and] H; clear H.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
assert (~ MF.expo m x y0).
unfold expf in H0.
tauto.
generalize (MF.degree_sum_bound m x y0 H2 H4 H H7).
intro.
unfold MAX in b.
omega.
