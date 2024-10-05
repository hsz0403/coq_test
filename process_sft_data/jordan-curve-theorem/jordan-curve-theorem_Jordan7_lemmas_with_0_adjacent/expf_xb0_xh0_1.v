Require Export Jordan6.

Lemma expf_xb0_xh0_1:forall (m:fmap)(x:dart), inv_hmap m -> exd m x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in expf m xb0 xh0_1.
Proof.
intros.
assert (xh0 = cA_1 m zero xb0).
unfold xb0 in |- *.
unfold xh0 in |- *.
rewrite cA_1_bottom in |- *.
tauto.
tauto.
tauto.
unfold xh0_1 in |- *.
rewrite H1 in |- *.
assert (exd m xb0).
unfold xb0 in |- *.
apply exd_bottom.
tauto.
tauto.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
assert (MF.f = cF).
tauto.
fold (cF m xb0) in |- *.
rewrite H3 in |- *.
split with 1%nat.
simpl in |- *.
tauto.
