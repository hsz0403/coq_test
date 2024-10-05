Require Export Jordan6.

Lemma B_B : forall (m:fmap)(k j:dim)(u v:dart), B (B m k u) j v = B (B m j v) k u.
Proof.
intros.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHm.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dim_dec d j).
elim (eq_dart_dec d0 u).
elim (eq_dart_dec d0 v).
intros.
rewrite <- a.
rewrite <- a0.
rewrite <- a1; rewrite a2.
tauto.
intro.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 u).
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
elim (eq_dart_dec d0 v).
tauto.
simpl in |- *.
elim (eq_dart_dec d0 u).
tauto.
elim (eq_dim_dec d k).
rewrite IHm.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 u).
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
tauto.
rewrite IHm.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
elim (eq_dart_dec d0 v).
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
rewrite IHm.
tauto.
simpl in |- *.
elim (eq_dim_dec d k).
tauto.
rewrite IHm.
tauto.
