Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Lemma expf_L_B:forall(m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> (expf (L (B m k x) k x (A m k x)) z t <-> expf m z t).
Proof.
intros.
unfold expf in |- *.
unfold MF.expo in |- *.
assert (MF.f = cF).
tauto.
rewrite H1 in |- *.
simpl in |- *.
split.
intros.
decompose [and] H2.
clear H2.
split.
tauto.
split.
generalize (exd_B m k x z).
tauto.
elim H7.
intros i Hi.
rewrite Iter_cF_L_B in Hi.
split with i.
tauto.
tauto.
tauto.
intros.
decompose [and] H2.
clear H2.
split.
split.
apply inv_hmap_B.
tauto.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
assert (exd m (A m k x)).
apply succ_exd_A.
tauto.
tauto.
split.
generalize (exd_B m k x x).
tauto.
split.
generalize (exd_B m k x (A m k x)).
tauto.
split.
rewrite A_B in |- *.
tauto.
tauto.
split.
rewrite A_1_B in |- *.
tauto.
tauto.
rewrite cA_B in |- *.
elim (eq_dart_dec x x).
intro.
apply succ_bottom.
tauto.
tauto.
tauto.
tauto.
tauto.
split.
generalize (exd_B m k x z).
tauto.
elim H6.
intros i Hi.
split with i.
rewrite Iter_cF_L_B in |- *.
tauto.
tauto.
tauto.
