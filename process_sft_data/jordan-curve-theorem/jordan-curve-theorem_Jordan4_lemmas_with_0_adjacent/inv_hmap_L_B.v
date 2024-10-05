Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma inv_hmap_L_B:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> inv_hmap (L (B m k x) k x (A m k x)).
Proof.
intros.
simpl in |- *.
unfold prec_L in |- *.
split.
generalize (inv_hmap_B m k x).
tauto.
split.
generalize (exd_B m k x x).
generalize (succ_exd m k x).
tauto.
split.
generalize (exd_B m k x (A m k x)).
generalize (succ_exd_A m k x).
tauto.
split.
unfold succ in |- *.
rewrite A_B.
tauto.
tauto.
split.
unfold pred in |- *.
rewrite A_1_B.
tauto.
tauto.
unfold succ in H0.
rewrite cA_B.
elim (eq_dart_dec x x).
intro.
apply succ_bottom.
tauto.
unfold succ in |- *.
tauto.
tauto.
tauto.
unfold succ in |- *.
tauto.
