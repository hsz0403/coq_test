Require Export Jordan6.

Lemma expf_B0_CS_1_c:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in expf m x0 xb0 -> (~ expf m x_1 z /\ expf m z t) -> expf (B m zero x) z t.
Proof.
intros.
decompose [and] H2.
clear H2.
unfold expf in H4.
unfold MF.expo in H4.
decompose [and] H4.
clear H4.
elim H7.
intros i Hi; clear H7.
rewrite <- Hi in |- *.
apply expf_B0_CS_1_c_prel.
tauto.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold x_1 in |- *.
tauto.
