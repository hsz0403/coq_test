Require Export Jordan6.

Lemma expf_B0_CS_1_b_aux:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> exd m z -> exd m t -> let x0 := cA m zero x in let xb0 := bottom m zero x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in expf m x0 xb0 -> (betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0) -> expf (B m zero x) z t.
Proof.
intros.
assert (expf (B m zero x) xh0_1 z).
unfold xh0_1 in |- *; unfold xh0 in |- *.
apply expf_B0_CS_1_b_prel2.
tauto.
tauto.
fold xb0 in |- *; fold x0 in |- *.
tauto.
fold x0 in |- *; fold xh0 in |- *; fold xh0_1 in |- *.
tauto.
assert (expf (B m zero x) xh0_1 t).
unfold xh0_1 in |- *; unfold xh0 in |- *.
apply expf_B0_CS_1_b_prel2.
tauto.
tauto.
fold xb0 in |- *; fold x0 in |- *.
tauto.
fold x0 in |- *; fold xh0 in |- *; fold xh0_1 in |- *.
tauto.
apply expf_trans with xh0_1.
apply expf_symm.
tauto.
tauto.
