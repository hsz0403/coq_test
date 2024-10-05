Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Theorem eqc_B: forall(m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> let xk:= A m k x in let m0:= B m k x in (eqc m z t <-> (eqc m0 z t \/ eqc m0 z x /\ eqc m0 xk t \/ eqc m0 z xk /\ eqc m0 x t)).
Proof.
simpl in |- *.
intros.
split.
apply eqc_B_CN.
tauto.
tauto.
apply eqc_B_CS.
tauto.
tauto.
