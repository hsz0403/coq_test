Require Export Jordan3.
Definition expfo(m:fmap)(x:dart)(z t:dart):= expf (L (B m zero x) zero x (A m zero x)) z t.
Definition eqco(m:fmap)(k:dim)(x z t:dart):= eqc (L (B m k x) k x (A m k x)) z t.

Lemma A_L_B:forall (m:fmap)(k j:dim)(x z:dart), inv_hmap m -> succ m k x -> let y:= A m k x in A (L (B m k x) k x y) j z = A m j z.
Proof.
induction m.
simpl in |- *.
intros.
unfold succ in H0.
simpl in H0.
tauto.
simpl in |- *.
unfold prec_I in |- *.
unfold succ in |- *.
intros.
elim (eq_dim_dec k j).
elim (eq_dart_dec x z).
intro.
rewrite a.
intro.
rewrite a0.
tauto.
intros.
rewrite a.
rewrite A_B_bis.
tauto.
intro.
symmetry in H1.
tauto.
intro.
rewrite A_B_ter.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
intros.
elim (eq_dim_dec k j).
elim (eq_dim_dec d k).
intros.
rewrite a.
rewrite a0.
elim (eq_dim_dec j j).
intro.
elim (eq_dart_dec x z).
intro.
rewrite a2.
tauto.
elim (eq_dart_dec d0 x).
elim (eq_dart_dec d0 z).
intros.
rewrite a3 in a2.
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec j j).
intros.
rewrite A_B_bis.
tauto.
intro.
symmetry in H1.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dart_dec x z).
intros.
rewrite <- a0.
elim (eq_dim_dec d k).
tauto.
rewrite a.
tauto.
intros.
rewrite <- a.
rewrite A_B_bis.
tauto.
intro.
symmetry in H1.
tauto.
elim (eq_dim_dec d k).
elim (eq_dim_dec d j).
intros.
rewrite a0 in a.
tauto.
elim (eq_dart_dec d0 x).
tauto.
simpl in |- *.
elim (eq_dim_dec d j).
tauto.
intros.
rewrite A_B_ter.
tauto.
tauto.
simpl in |- *.
intros.
rewrite A_B_ter.
tauto.
tauto.
