Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_expf_L0_2_bis:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> let x_1 := cA_1 m one x in ~ expf m x_1 y -> ~ expf m x_1 z -> ~ expf m y z -> expf m z t -> expf (L m zero x y) z t.
Proof.
intros.
unfold expf in H4.
unfold MF.expo in H4.
decompose [and] H4.
clear H4.
elim H8.
clear H8.
intros i Hi.
rewrite <- Hi in |- *.
assert (MF.f = cF).
tauto.
rewrite H4 in |- *.
apply expf_expf_L0_2.
tauto.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
tauto.
