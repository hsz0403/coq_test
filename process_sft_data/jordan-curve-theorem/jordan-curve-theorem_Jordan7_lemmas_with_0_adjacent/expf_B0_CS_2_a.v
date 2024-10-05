Require Export Jordan6.

Lemma expf_B0_CS_2_a:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> (expf m x_1 z \/ expf m xh0_1 z) /\ (expf m x_1 t \/ expf m xh0_1 t) -> expf (B m zero x) z t.
Proof.
intros.
decompose [and] H2.
clear H2.
elim H3.
clear H3.
elim H4.
clear H4.
intros.
apply expf_B0_CS_2_a_I.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
clear H4.
intros.
apply expf_B0_CS_2_a_IV.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
clear H3.
elim H4.
clear H4.
intros.
apply expf_B0_CS_2_a_III.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold xh0 in |- *; fold xh0_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
clear H4.
intros.
apply expf_B0_CS_2_a_II.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
