Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma degree_L1_merge_MAX: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> ~expf m x y0 -> let MAX := MF.degree m x + MF.degree m y0 in MF.degree_aux m1 x MAX = MAX.
Proof.
intros.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
rewrite ndN_L in |- *.
set (dx := MF.degree m x) in |- *.
set (dy0 := MF.degree m y0) in |- *.
fold dx in MAX.
fold dy0 in MAX.
elim (le_lt_dec MAX (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f (L m one x y)) MAX x)).
tauto.
intro.
elim b.
unfold MAX in |- *.
unfold dx in |- *.
unfold dy0 in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H1 in |- *.
symmetry in |- *.
unfold y0 in |- *.
apply cF_L1_y0.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
fold y0 in |- *.
tauto.
intro.
unfold MAX in b.
unfold m1 in H.
simpl in H.
assert (inv_hmap m).
tauto.
unfold prec_L in H.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
unfold expf in H0.
assert (~ MF.expo m x y0).
tauto.
generalize (MF.degree_sum_bound m x y0 H1 H2 H4 H5).
fold dy0 in |- *.
fold dx in |- *.
omega.
