Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma eqco_eqc:forall(m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> (eqco m k x z t <-> eqc m z t).
Proof.
unfold eqco in |- *.
simpl in |- *.
intros.
generalize (eqc_B m k x z t H H0).
simpl in |- *.
tauto.
