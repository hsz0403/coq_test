Require Export Jordan6.

Lemma expf_B0_CS_1:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in expf m x0 xb0 -> (betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0 \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t) -> expf (B m zero x) z t.
Proof.
intros.
elim H2.
clear H2.
intro.
apply expf_B0_CS_1_a.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xb0 in |- *.
tauto.
clear H2.
intro.
elim H2.
clear H2.
intro.
apply expf_B0_CS_1_b.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold x0 in |- *.
tauto.
clear H2.
intro.
apply expf_B0_CS_1_c.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
tauto.
