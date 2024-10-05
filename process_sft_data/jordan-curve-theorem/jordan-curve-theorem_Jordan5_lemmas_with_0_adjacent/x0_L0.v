Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma x0_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> cA m zero x = bottom m1 zero x.
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec y (bottom m zero x)).
intros.
unfold prec_L in H.
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
unfold prec_L in H.
intro.
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
