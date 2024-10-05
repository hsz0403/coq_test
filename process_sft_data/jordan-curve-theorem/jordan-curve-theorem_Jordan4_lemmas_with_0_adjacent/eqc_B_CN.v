Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma eqc_B_CN: forall(m:fmap)(k:dim)(x z t:dart), inv_hmap m -> succ m k x -> let xk:= A m k x in let m0:= B m k x in eqc m z t -> (eqc m0 z t \/ eqc m0 z x /\ eqc m0 xk t \/ eqc m0 z xk /\ eqc m0 x t).
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
unfold succ in IHm.
intros.
unfold prec_I in H.
decompose [and] H.
clear H.
generalize (IHm k x z t H2 H0).
intros.
intuition.
unfold succ in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
generalize H0.
clear H0.
decompose [and] H.
clear H.
rename d into j.
elim (eq_dim_dec j k).
elim (eq_dart_dec d0 x).
intros.
rewrite <- a.
tauto.
simpl in |- *.
intros.
unfold succ in IHm.
elim H1.
intro.
generalize (IHm k x z t H0 H6 H).
tauto.
intro.
elim H.
intros.
decompose [and] H8.
clear H8.
clear H1.
generalize (IHm k x z d0 H0 H6 H9).
generalize (IHm k x d1 t H0 H6 H10).
intros.
elim H1.
elim H8.
intros.
tauto.
intros.
elim H11.
intros.
clear H11.
tauto.
intro.
clear H11.
tauto.
intros.
elim H11.
clear H11.
intro.
elim H8.
intro.
tauto.
intro.
elim H12.
clear H12.
intro.
tauto.
intro.
clear H12.
assert (eqc (B m k x) z t).
apply eqc_trans with (A m k x).
tauto.
tauto.
tauto.
intro.
clear H11.
elim H8.
intro.
tauto.
intro.
elim H11.
clear H11.
intro.
assert (eqc (B m k x) z t).
apply eqc_trans with x.
tauto.
tauto.
tauto.
intro.
clear H11.
tauto.
intro.
clear H.
clear H1.
decompose [and] H8.
clear H8.
generalize (IHm k x z d1 H0 H6 H).
generalize (IHm k x d0 t H0 H6 H1).
intros.
elim H8.
intro.
elim H9.
intro.
tauto.
intro.
elim H11.
clear H11.
intro.
tauto.
clear H11.
intro.
tauto.
intro.
elim H10.
clear H10.
intro.
elim H9.
intro.
tauto.
intro.
elim H11.
clear H11.
intro.
tauto.
clear H11.
intro.
assert (eqc (B m k x) z t).
apply eqc_trans with (A m k x).
tauto.
tauto.
tauto.
intro.
clear H10.
elim H9.
intro.
tauto.
intro.
elim H10.
clear H10.
intro.
assert (eqc (B m k x) z t).
apply eqc_trans with x.
tauto.
tauto.
tauto.
elim H10.
clear H10.
intro.
tauto.
tauto.
simpl in |- *.
intros.
unfold succ in IHm.
elim H1.
intro.
generalize (IHm k x z t H0 H6 H).
tauto.
intro.
elim H.
intros.
decompose [and] H8.
clear H8.
clear H1.
generalize (IHm k x z d0 H0 H6 H9).
generalize (IHm k x d1 t H0 H6 H10).
intros.
elim H1.
elim H8.
intros.
tauto.
intros.
elim H11.
intros.
clear H11.
tauto.
intro.
clear H11.
tauto.
intros.
elim H11.
clear H11.
intro.
elim H8.
intro.
tauto.
intro.
elim H12.
clear H12.
intro.
tauto.
intro.
clear H12.
assert (eqc (B m k x) z t).
apply eqc_trans with (A m k x).
tauto.
tauto.
tauto.
intro.
clear H11.
elim H8.
intro.
tauto.
intro.
elim H11.
clear H11.
intro.
assert (eqc (B m k x) z t).
apply eqc_trans with x.
tauto.
tauto.
tauto.
intro.
clear H11.
tauto.
intro.
clear H.
clear H1.
decompose [and] H8.
clear H8.
generalize (IHm k x z d1 H0 H6 H).
generalize (IHm k x d0 t H0 H6 H1).
intros.
elim H8.
intro.
elim H9.
intro.
tauto.
intro.
elim H11.
clear H11.
intro.
tauto.
clear H11.
intro.
tauto.
intro.
elim H10.
clear H10.
intro.
elim H9.
intro.
tauto.
intro.
elim H11.
clear H11.
intro.
tauto.
clear H11.
intro.
assert (eqc (B m k x) z t).
apply eqc_trans with (A m k x).
tauto.
tauto.
tauto.
intro.
clear H10.
elim H9.
intro.
tauto.
intro.
elim H10.
clear H10.
intro.
assert (eqc (B m k x) z t).
apply eqc_trans with x.
tauto.
tauto.
tauto.
elim H10.
clear H10.
intro.
tauto.
tauto.
