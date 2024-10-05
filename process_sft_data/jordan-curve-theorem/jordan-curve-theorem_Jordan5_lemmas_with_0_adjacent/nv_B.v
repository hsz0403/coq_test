Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma nv_B:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> nv (B m k x) = nv m + if (eq_dim_dec k one) then 1 else 0.
Proof.
intros.
induction m.
unfold succ in H0.
simpl in H0.
tauto.
unfold succ in H0.
simpl in H0.
simpl in |- *.
simpl in H.
assert (nv (B m k x) = nv m + (if eq_dim_dec k one then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
omega.
simpl in H.
unfold succ in H0.
simpl in H0.
generalize H0.
clear H0.
simpl in |- *.
elim (eq_dim_dec d k).
intro.
elim (eq_dart_dec d0 x).
intros.
rewrite a.
elim k.
elim (eq_dim_dec zero one).
intro.
inversion a1.
intro.
omega.
elim (eq_dim_dec one one).
intro.
omega.
tauto.
simpl in |- *.
intros H1 H2.
assert (nv (B m k x) = nv m + (if eq_dim_dec k one then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H0.
clear H0.
rewrite a.
rewrite a in H.
induction k.
tauto.
intros.
omega.
simpl in |- *.
intros H1 H2.
elim d.
apply IHm.
tauto.
unfold succ in |- *.
tauto.
assert (nv (B m k x) = nv m + (if eq_dim_dec k one then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
omega.
