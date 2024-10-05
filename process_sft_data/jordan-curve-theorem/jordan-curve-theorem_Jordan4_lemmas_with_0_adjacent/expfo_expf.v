Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma expfo_expf:forall(m:fmap)(x:dart)(z t:dart), inv_hmap m -> succ m zero x -> (expfo m x z t <-> expf m z t).
Proof.
unfold expfo in |- *.
unfold expf in |- *.
unfold MF.expo in |- *.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
unfold MF.f in |- *.
unfold McF.f in |- *.
assert (exd m x).
apply succ_exd with zero.
tauto.
unfold succ in |- *.
tauto.
split.
intros.
decompose [and] H2.
clear H2.
split.
tauto.
generalize (exd_B m zero x z).
split.
tauto.
elim H11.
intros i Hi.
split with i.
rewrite Iter_cF_L_B in Hi.
tauto.
tauto.
tauto.
unfold succ in |- *.
intro.
decompose [and] H2.
clear H2.
split.
split.
apply inv_hmap_B.
tauto.
split.
generalize (exd_B m zero x x).
tauto.
split.
generalize (exd_B m zero x (A m zero x)).
assert (exd m (A m zero x)).
apply succ_exd_A.
tauto.
tauto.
tauto.
split.
rewrite A_B.
tauto.
tauto.
split.
rewrite A_1_B.
tauto.
tauto.
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
split.
generalize (exd_B m zero x z).
tauto.
elim H6.
intros i Hi.
split with i.
rewrite Iter_cF_L_B.
tauto.
tauto.
tauto.
