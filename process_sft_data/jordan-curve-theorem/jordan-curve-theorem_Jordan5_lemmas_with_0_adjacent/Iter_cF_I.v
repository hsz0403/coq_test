Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma Iter_cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point)(i:nat), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> Iter (cF (I m x u p)) i z = Iter (cF m) i z.
Proof.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
intros.
rewrite IHi.
rewrite cF_I.
tauto.
tauto.
tauto.
assert (MF.f = cF).
tauto.
rewrite <- H3.
generalize (MF.exd_Iter_f m i z).
tauto.
intro.
unfold prec_I in H0.
rewrite H3 in H0.
generalize (MF.exd_Iter_f m i z).
tauto.
tauto.
tauto.
tauto.
tauto.
