Require Export Jordan6.

Lemma expf_B0_CS_2:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in ~expf m x0 xb0 -> (expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t) -> expf (B m zero x) z t.
intros.
intros.
set (x_1 := cA_1 m one x) in |- *.
set (xh0 := top m zero x) in |- *.
set (xh0_1 := cA_1 m one xh0) in |- *.
assert ((expf m x_1 z \/ expf m xh0_1 z) /\ (expf m x_1 t \/ expf m xh0_1 t) \/ expf m z t /\ ~ expf m x_1 z /\ ~ expf m xh0_1 z).
unfold x_1 in |- *; unfold xh0_1 in |- *; unfold xh0 in |- *.
apply expf_transfert.
tauto.
apply succ_exd with zero.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold xb0 in |- *.
fold x0 in |- *.
tauto.
apply expf_B0_CS_2_aux.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
