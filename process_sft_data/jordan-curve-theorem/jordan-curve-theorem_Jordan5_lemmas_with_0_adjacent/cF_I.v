Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> (cF (I m x u p) z = cF m z).
Proof.
unfold cF in |- *.
intros.
rewrite cA_1_I.
rewrite cA_1_I.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dart_dec x z).
tauto.
intro.
intro.
unfold prec_I in H0.
generalize (exd_cA_1 m zero z).
rewrite <- H3.
tauto.
