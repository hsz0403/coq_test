Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_I:forall(m:fmap)(x z t:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> (expf (I m x u p) z t <-> expf m z t).
Proof.
intros.
unfold expf in |- *.
unfold MF.expo in |- *.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H3.
split.
intros.
decompose [and] H4.
clear H4.
elim H9.
intros i Eq.
split.
tauto.
split.
tauto.
split with i.
generalize (Iter_cF_I m x z u p i H7 H8 H1 H2).
intro.
rewrite <- H4.
tauto.
intros.
decompose [and] H4.
clear H4.
split.
tauto.
split.
tauto.
elim H8.
intros i Hi.
split with i.
rewrite Iter_cF_I.
tauto.
tauto.
tauto.
tauto.
tauto.
