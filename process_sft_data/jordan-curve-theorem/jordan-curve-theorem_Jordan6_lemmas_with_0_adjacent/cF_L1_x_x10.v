Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1_x_x10:forall(m:fmap)(x y:dart)(i:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let dx := MF.degree m x in let m1:= L m one x y in ~expf m x y0 -> i <= dx - 1 -> Iter (cF m1) i x = Iter (cF m) i x.
Proof.
intros.
unfold prec_L in H0.
assert (exd m x).
tauto.
generalize (MF.degree_lub m x H H3).
simpl in |- *.
fold dx in |- *.
intros.
decompose [and] H4.
clear H4.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H4 in H8.
rewrite <- H4 in H7.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
set (x10 := cF_1 m x) in |- *.
set (y_1 := cA_1 m one y) in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 (Iter (cF m) i x)).
intro.
elim H1.
rewrite a in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
rewrite <- H4 in |- *.
split with i.
tauto.
elim (eq_dart_dec x10 (Iter (cF m) i x)).
intros.
assert (i = dx - 1).
apply (MF.unicity_mod_p m x i (dx - 1) H H3).
assert (MF.Iter_upb m x = dx).
unfold dx in |- *.
apply MF.upb_eq_degree.
tauto.
tauto.
rewrite H6 in |- *.
omega.
rewrite MF.upb_eq_degree in |- *.
fold dx in |- *.
omega.
tauto.
tauto.
rewrite <- H4 in |- *.
rewrite <- a in |- *.
unfold x10 in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite H6 in |- *.
rewrite H4 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite <- H4 in |- *.
rewrite H7 in |- *.
tauto.
tauto.
tauto.
omega.
absurd (i = dx - 1).
omega.
tauto.
intros.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
omega.
