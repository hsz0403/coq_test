Require Export Jordan6.

Lemma inv_hmap_L0L0:forall (m:fmap)(x y x' y':dart), let m1:= L (L m zero x y) zero x' y' in let m2:= L (L m zero x' y') zero x y in inv_hmap m1 -> inv_hmap m2.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
intros.
decompose [and] H.
clear H.
generalize H8 H9 H11.
clear H8 H9 H11.
elim (eq_dart_dec x x').
intros.
absurd (y <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec y y').
intros.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m zero y) x').
intros.
intros.
split.
assert (cA m zero x' <> y').
intro.
rewrite <- a in H.
rewrite cA_cA_1 in H.
tauto.
tauto.
tauto.
tauto.
split.
tauto.
split.
tauto.
elim (eq_dart_dec x' x).
intro.
symmetry in a0.
tauto.
elim (eq_dart_dec y' y).
intro.
symmetry in a0.
tauto.
elim (eq_dart_dec (cA_1 m zero y') x).
intro.
rewrite <- a0 in H11.
rewrite cA_cA_1 in H11.
tauto.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec x' x).
intro.
symmetry in a.
tauto.
elim (eq_dart_dec y' y).
intro.
symmetry in a.
tauto.
elim (eq_dart_dec (cA_1 m zero y') x).
intro.
assert (cA m zero x' <> y).
intro.
rewrite <- H in b.
rewrite cA_1_cA in b.
tauto.
tauto.
tauto.
tauto.
tauto.
