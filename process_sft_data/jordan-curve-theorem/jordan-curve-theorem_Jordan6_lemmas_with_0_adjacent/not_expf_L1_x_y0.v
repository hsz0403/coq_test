Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma not_expf_L1_x_y0:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let y0 := cA m zero y in let y_1 := cA_1 m one y in expf m x y0 -> ~expf (L m one x y) x y_1.
Proof.
intros.
assert (expf m x y0).
tauto.
rename H2 into E1.
intro.
unfold expf in H1.
assert (MF.expo1 m x y0).
generalize (MF.expo_expo1 m x y0).
tauto.
unfold MF.expo1 in H3.
elim H3.
intros.
clear H3.
elim H5.
intros j0 Hj.
decompose [and] Hj.
clear H5 Hj.
set (p := MF.Iter_upb m x) in |- *.
fold p in H3.
assert (expf m y0 y_1).
apply (expf_y0_y_1 m x y).
tauto.
simpl in H.
tauto.
assert (y_1 <> x).
intro.
assert (cA m one x = y).
rewrite <- H7 in |- *.
unfold y_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
simpl in H.
unfold prec_L in H.
tauto.
simpl in H; unfold prec_L in H; tauto.
assert (y_1 = cF m y0).
unfold y0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
simpl in H; unfold prec_L in H; tauto.
assert (Iter (MF.f m) (S j0) x = y_1).
simpl in |- *.
rewrite H6 in |- *.
symmetry in |- *.
tauto.
assert (S j0 <> p).
intro.
rewrite H10 in H9.
unfold p in H9.
rewrite MF.Iter_upb_period in H9.
symmetry in H9.
tauto.
tauto.
simpl in H; unfold prec_L in H; tauto.
set (m1 := L m one x y) in |- *.
fold m1 in H2.
assert (MF.f = cF).
tauto.
assert (expf m1 x y_1).
tauto.
unfold expf in H12.
assert (MF.expo1 m1 x y_1).
generalize (MF.expo_expo1 m1 x y_1).
tauto.
unfold MF.expo1 in H13.
elim H13.
intros.
clear H13.
elim H15.
intros i Hi.
clear H15.
elim Hi.
intros.
clear Hi.
set (p1 := MF.Iter_upb m1 x) in |- *.
fold p1 in H13.
assert (inv_hmap (L m one x y)).
tauto.
generalize (degree_L1_split m x y H16 E1).
fold y_1 in |- *.
fold m1 in |- *.
fold p in |- *.
assert (MF.Iter_upb m x = MF.degree m x).
apply (MF.upb_eq_degree m x).
tauto.
tauto.
assert (MF.Iter_upb m1 x = MF.degree m1 x).
apply (MF.upb_eq_degree m1 x).
tauto.
tauto.
intro.
assert (MF.degree m x = MF.degree m1 x + MF.degree m1 y_1).
tauto.
rewrite <- H17 in H19.
rewrite <- H18 in H19.
fold p in H19.
fold p1 in H19.
assert (p1 = j0 + 1).
unfold p1 in |- *.
rewrite H18 in |- *.
unfold m1 in |- *.
apply degree_L1_split_x_y0.
fold y0 in |- *.
symmetry in |- *.
tauto.
tauto.
rewrite <- H17 in |- *.
fold p in |- *.
omega.
fold y0 in |- *.
tauto.
assert (Iter (MF.f m) i x = y_1).
rewrite H11 in |- *.
rewrite <- (cF_L1_x_y0 m x y i j0) in |- *.
fold m1 in |- *.
rewrite <- H11 in |- *.
tauto.
tauto.
simpl in H.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H17 in |- *.
fold p in |- *.
omega.
assert (i = S j0).
apply (MF.unicity_mod_p m x).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H9 in |- *.
tauto.
absurd (i = S j0).
omega.
tauto.
