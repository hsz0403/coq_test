Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma cF_L_B:forall (m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> let y:= A m k x in cF (L (B m k x) k x y) z = cF m z.
Proof.
simpl in |- *.
unfold cF in |- *.
intros.
rewrite cA_1_L_B.
rewrite cA_1_L_B.
tauto.
tauto.
tauto.
tauto.
tauto.
