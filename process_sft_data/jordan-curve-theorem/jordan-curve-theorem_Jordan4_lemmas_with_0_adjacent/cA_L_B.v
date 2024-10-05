Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma cA_L_B:forall (m:fmap)(k j:dim)(x z:dart), inv_hmap m -> succ m k x -> let y:= A m k x in cA (L (B m k x) k x y) j z = cA m j z.
Proof.
simpl in |- *.
intros.
elim (eq_dim_dec k j).
intro.
elim (eq_dart_dec x z).
rewrite a.
intro.
rewrite a0.
rewrite a0 in H0.
generalize (A_cA m j z (A m j z)).
intros.
symmetry in |- *.
apply H1.
tauto.
apply succ_exd with k.
tauto.
tauto.
apply succ_exd_A.
tauto.
rewrite <- a.
tauto.
tauto.
intro.
elim (eq_dart_dec (cA_1 (B m k x) j (A m k x)) z).
intro.
rewrite <- a.
rewrite <- a in a0.
rewrite cA_1_B in a0.
generalize a0.
clear a0.
elim (eq_dart_dec (A m k x) (A m k x)).
intros.
rewrite <- a1.
rewrite cA_top.
rewrite cA_B.
elim (eq_dart_dec x x).
tauto.
tauto.
tauto.
tauto.
tauto.
apply succ_exd with k.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite <- a.
rewrite cA_B.
elim (eq_dart_dec x z).
tauto.
intro.
elim (eq_dart_dec (top m k x) z).
intro.
rewrite <- a in b0.
rewrite cA_1_B in b0.
generalize b0.
elim (eq_dart_dec (A m k x) (A m k x)).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
rewrite cA_B_ter.
tauto.
tauto.
tauto.
