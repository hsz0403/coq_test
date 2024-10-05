Require Export Jordan6.

Lemma expf_B0_CS_2_b:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf m z t -> ~expf m x_1 z -> ~expf m xh0_1 z -> expf (B m zero x) z t.
Proof.
intros.
unfold expf in H2.
decompose [and] H2.
clear H2.
unfold MF.expo in H6.
elim H6.
intros.
clear H6.
elim H7.
clear H7.
intros i Hi.
rewrite <- Hi in |- *.
apply expf_B0_CS_2_b_ind.
tauto.
tauto.
tauto.
fold xb0 in |- *.
fold x0 in |- *; tauto.
fold x_1 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
