Require Export Jordan6.

Lemma expf_x0_x_1:forall (m:fmap)(x:dart), inv_hmap m -> exd m x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in expf m x0 x_1.
Proof.
intros.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
unfold x_1 in |- *.
rewrite H1 in |- *.
fold (cF m x0) in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
assert (MF.f = cF).
tauto.
rewrite H2 in |- *.
split with 1%nat.
simpl in |- *.
tauto.
