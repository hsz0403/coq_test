Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma eqc_B_eqc :forall(m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> eqc (B m k x) z t -> eqc m z t.
Proof.
unfold succ in |- *.
induction m.
simpl in |- *.
tauto.
rename t into u.
simpl in |- *.
unfold prec_I in |- *.
intros.
decompose [and] H.
clear H.
elim H1.
intro.
tauto.
intro.
right.
apply (IHm k x z t H2 H0 H).
simpl in |- *.
unfold prec_L in |- *.
intros k x z t H.
decompose [and] H.
clear H.
rename d into j.
elim (eq_dim_dec j k).
elim (eq_dart_dec d0 x).
intros.
tauto.
simpl in |- *.
intros.
intuition.
left.
apply (IHm k x z t).
tauto.
tauto.
tauto.
right.
left.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
simpl in |- *.
intros.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
generalize (IHm k x z t H0 H).
tauto.
