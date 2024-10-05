Require Export Jordan6.

Lemma expf_B0_CS_1_a_aux:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> exd m z -> exd m t -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in expf m x0 xb0 -> (betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0) -> expf (B m zero x) z t.
Proof.
intros.
assert (expf (B m zero x) x_1 z).
unfold x_1 in |- *.
apply expf_B0_CS_1_a_prel2.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xb0 in |- *.
tauto.
assert (expf (B m zero x) x_1 t).
unfold x_1 in |- *.
apply expf_B0_CS_1_a_prel2.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xb0 in |- *.
tauto.
generalize H5 H6.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with x_1.
apply MF.expo_symm.
tauto.
tauto.
tauto.
