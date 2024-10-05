Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma y_0_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> cA_1 m zero y = top m1 zero x.
Proof.
simpl in |- *.
unfold prec_L in |- *.
intros.
rewrite cA_1_top.
elim (eq_dart_dec x (top m zero x)).
tauto.
intro.
rewrite nosucc_top in b.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
