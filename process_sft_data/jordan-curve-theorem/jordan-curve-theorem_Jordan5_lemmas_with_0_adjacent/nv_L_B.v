Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma nv_L_B:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let m1 := L (B m k x) k x (A m k x) in nv m1 = nv m.
Proof.
intros.
generalize (nv_B m k x H H0).
induction k.
elim (eq_dim_dec zero one).
unfold m1 in |- *.
intro.
inversion a.
unfold m1 in |- *.
simpl in |- *.
intros.
omega.
unfold m1 in |- *.
simpl in |- *.
intros.
omega.
