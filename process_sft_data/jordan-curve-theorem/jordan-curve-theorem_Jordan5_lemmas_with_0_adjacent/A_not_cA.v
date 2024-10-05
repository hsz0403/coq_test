Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma A_not_cA: forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> A m k x <> cA (B m k x) k x.
Proof.
intros.
generalize (succ_bottom m k x H H0).
intro.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
generalize (cA_B m k x x H H0).
elim (eq_dart_dec x x).
intros.
rewrite H3.
intro.
symmetry in H4.
tauto.
tauto.
