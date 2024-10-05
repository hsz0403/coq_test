Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma not_expf_L1_x: forall(m:fmap)(x y z:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> ~expf m1 x z.
Proof.
intros.
intro.
assert (MF.expo1 m1 x z).
unfold expf in H3.
generalize (MF.expo_expo1 m1 x z).
tauto.
unfold MF.expo1 in H4.
decompose [and] H4.
clear H4.
elim H6.
intros i Hi.
unfold m1 in Hi.
rewrite MF.upb_eq_degree in Hi.
rewrite degree_L1_merge_x in Hi.
set (dx := MF.degree m x) in |- *.
fold y0 in Hi.
set (dy0 := MF.degree m y0) in Hi.
fold dx in Hi.
decompose [and] Hi.
clear Hi H6.
elim H1.
unfold expf in |- *.
split.
unfold m1 in H.
simpl in H.
tauto.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
decompose [and] H6.
clear H6.
assert (cF = MF.f).
tauto.
elim (le_lt_dec i (dx - 1)).
intro.
unfold MF.expo in |- *.
split.
tauto.
rewrite <- H6 in |- *.
split with i.
rewrite <- (cF_L1_x_x10 m x y i) in |- *.
rewrite H6 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
intro.
elim (le_lt_dec i (dx + (dy0 - 1))).
intro.
elim H2.
unfold expf in |- *.
split.
tauto.
set (y_1 := cA_1 m one y) in |- *.
assert (MF.expo m y0 y_1).
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
split with 1.
simpl in |- *.
rewrite <- H6 in |- *.
unfold y0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
apply MF.expo_trans with y_1.
tauto.
unfold MF.expo in |- *.
split.
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
tauto.
split with (i - dx).
rewrite <- H6 in |- *.
unfold y_1 in |- *.
rewrite <- (cF_L1_y_1_y0 m x y (i - dx)) in |- *.
fold dx in |- *.
assert (dx + (i - dx) = i).
omega.
rewrite H15 in |- *.
fold m1 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
fold dy0 in |- *.
omega.
intro.
absurd (dx + (dy0 - 1) < i).
omega.
tauto.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold m1 in |- *.
tauto.
simpl in |- *.
tauto.
