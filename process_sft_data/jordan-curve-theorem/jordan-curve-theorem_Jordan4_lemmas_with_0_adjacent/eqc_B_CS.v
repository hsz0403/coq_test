Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma eqc_B_CS: forall(m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> let xk:= A m k x in let m0:= B m k x in (eqc m0 z t \/ eqc m0 z x /\ eqc m0 xk t \/ eqc m0 z xk /\ eqc m0 x t) -> eqc m z t.
Proof.
induction m.
simpl in |- *.
unfold succ in |- *.
simpl in |- *.
tauto.
rename t into u.
unfold succ in |- *.
simpl in |- *.
intros.
unfold prec_I in H.
decompose [and] H.
clear H.
generalize (IHm k x z t H2 H0).
simpl in |- *.
intros.
assert (x <> d).
intro.
rewrite <- H3 in H5.
apply H5.
apply succ_exd with k.
tauto.
tauto.
assert (A m k x <> d).
intro.
rewrite <- H6 in H5.
elim H5.
apply succ_exd_A.
tauto.
unfold succ in |- *.
tauto.
intuition.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros k x z t H.
unfold succ in IHm.
decompose [and] H.
clear H.
rename d into j.
elim (eq_dim_dec j k).
elim (eq_dart_dec d0 x).
intros.
rewrite a.
tauto.
simpl in |- *.
intros.
rewrite a in H6.
elim H5.
intro.
elim H7.
generalize (IHm k x z t H0 H).
tauto.
intro.
elim H8.
intro.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
intro.
clear H8.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
clear H5.
intro.
elim H5.
clear H5.
intro.
decompose [and or] H5.
clear H5.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x d1 t H0 H).
generalize (IHm k x z d0 H0 H).
tauto.
assert (eqc (B m k x) z t).
apply eqc_trans with d0.
tauto.
tauto.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
assert (eqc (B m k x) z t).
apply eqc_trans with d1.
tauto.
tauto.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
intro.
clear H5.
intuition.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
generalize (IHm k x d1 t H0 H).
generalize (IHm k x z d0 H0 H).
tauto.
assert (eqc (B m k x) z t).
apply eqc_trans with d0.
tauto.
tauto.
generalize (IHm k x z t H0 H).
tauto.
assert (eqc (B m k x) z t).
apply eqc_trans with d1.
tauto.
tauto.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
simpl in |- *.
intros.
elim H5.
intro.
elim H7.
generalize (IHm k x z t H0 H).
tauto.
intro.
elim H8.
intro.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
intro.
clear H8.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
clear H5.
intro.
elim H5.
clear H5.
intro.
decompose [and or] H5.
clear H5.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x d1 t H0 H).
generalize (IHm k x z d0 H0 H).
tauto.
assert (eqc (B m k x) z t).
apply eqc_trans with d0.
tauto.
tauto.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
assert (eqc (B m k x) z t).
apply eqc_trans with d1.
tauto.
tauto.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
intro.
clear H5.
intuition.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
generalize (IHm k x z d0 H0 H).
generalize (IHm k x d1 t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
generalize (IHm k x d1 t H0 H).
generalize (IHm k x z d0 H0 H).
tauto.
assert (eqc (B m k x) z t).
apply eqc_trans with d0.
tauto.
tauto.
generalize (IHm k x z t H0 H).
tauto.
assert (eqc (B m k x) z t).
apply eqc_trans with d1.
tauto.
tauto.
generalize (IHm k x z t H0 H).
tauto.
generalize (IHm k x z d1 H0 H).
generalize (IHm k x d0 t H0 H).
tauto.
