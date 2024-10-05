Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma Iter_cF_L_B: forall (m:fmap)(k:dim)(x:dart)(i:nat)( z:dart), inv_hmap m -> succ m k x -> let y:= A m k x in Iter (cF (L (B m k x) k x (A m k x))) i z = Iter (cF m) i z.
Proof.
intros.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi.
rewrite cF_L_B.
tauto.
tauto.
tauto.
