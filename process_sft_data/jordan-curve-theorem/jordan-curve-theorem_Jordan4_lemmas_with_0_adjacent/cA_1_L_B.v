Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma cA_1_L_B:forall(m : fmap)(k j : dim)(x z : dart), inv_hmap m -> succ m k x -> let y:= A m k x in cA_1 (L (B m k x) k x y) j z = cA_1 m j z.
Proof.
simpl in |- *.
intros.
elim (eq_dim_dec k j).
intro.
elim (eq_dart_dec (A m k x) z).
rewrite a in |- *.
intro.
rewrite <- a0 in |- *.
assert (cA m j x = A m j x).
apply A_cA.
tauto.
apply succ_exd with k.
tauto.
tauto.
rewrite <- a in |- *.
apply succ_exd_A.
tauto.
tauto.
tauto.
rewrite <- H1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply succ_exd with k.
tauto.
tauto.
elim (eq_dart_dec (cA (B m k x) j x) z).
intros.
rewrite <- a in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m k x) (A m k x)).
intros.
generalize a0.
clear a0.
rewrite <- a in |- *.
rewrite cA_B in |- *.
elim (eq_dart_dec x x).
intros.
rewrite <- a2 in |- *.
rewrite cA_1_bottom in |- *.
tauto.
tauto.
apply succ_exd with k.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intros.
rewrite <- a in |- *.
rewrite cA_1_B in |- *.
elim (eq_dart_dec (A m k x) z).
tauto.
elim (eq_dart_dec (bottom m k x) z).
intros.
rewrite <- a in b.
rewrite cA_B in b.
generalize b.
elim (eq_dart_dec x x).
tauto.
tauto.
tauto.
unfold succ in |- *.
unfold succ in H0.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite cA_1_B_ter in |- *.
tauto.
tauto.
tauto.
