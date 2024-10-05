Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma cA_1_I:forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> x <> z -> (cA_1 (I m x u p) k z = cA_1 m k z).
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
tauto.
tauto.
