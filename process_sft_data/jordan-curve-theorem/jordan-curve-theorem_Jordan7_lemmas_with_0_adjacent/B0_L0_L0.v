Require Export Jordan6.

Lemma B0_L0_L0:forall (m:fmap)(x y x' y':dart), let m1 := L (L m zero x y) zero x' y' in inv_hmap m1 -> B m1 zero x = L m zero x' y'.
Proof.
simpl in |- *.
intros.
decompose [and] H.
clear H.
unfold prec_L in H1.
unfold succ in H1.
unfold pred in H1.
simpl in H1.
decompose [and] H1.
clear H1.
generalize H0 H5.
clear H0 H5.
unfold prec_L in H3.
generalize H7.
clear H7.
unfold succ in H3.
unfold pred in H3.
decompose [and] H3.
clear H3.
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
elim (eq_dart_dec x' x).
intro.
rewrite a in |- *.
tauto.
elim (eq_dart_dec x x).
tauto.
tauto.
