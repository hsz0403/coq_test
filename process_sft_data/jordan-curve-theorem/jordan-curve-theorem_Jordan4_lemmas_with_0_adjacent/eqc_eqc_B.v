Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma eqc_eqc_B : forall(m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> eqc (B m k x) x (A m k x) -> eqc m z t -> eqc (B m k x) z t.
Proof.
intros.
generalize (eqc_B_CN m k x z t H H0 H2).
intro.
elim H3.
tauto.
clear H3.
intro.
elim H3.
clear H3.
intro.
apply eqc_trans with x.
tauto.
apply eqc_trans with (A m k x).
tauto.
tauto.
clear H3.
intro.
eapply eqc_trans with (A m k x).
tauto.
apply eqc_trans with x.
apply eqc_symm.
tauto.
tauto.
