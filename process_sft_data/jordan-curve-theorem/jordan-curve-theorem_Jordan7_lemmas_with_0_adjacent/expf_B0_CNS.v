Require Export Jordan6.

Theorem expf_B0_CNS:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> (expf (B m zero x) z t <-> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in (if expf_dec m x0 xb0 then betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0 \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t)).
Proof.
simpl in |- *.
split.
apply expf_B0_CN.
tauto.
tauto.
apply expf_B0_CS.
tauto.
tauto.
