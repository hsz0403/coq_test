Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma ndZ_L_B:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let m1:= L (B m k x) k x (A m k x) in nd m1 = nd m.
Proof.
simpl in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
unfold succ in IHm.
assert (nd (B m k x) = nd m).
apply IHm.
tauto.
tauto.
omega.
simpl in |- *.
unfold succ in |- *.
unfold succ in IHm.
unfold prec_L in |- *.
simpl in |- *.
intros k x H.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 x).
tauto.
simpl in |- *.
intros.
apply IHm.
tauto.
tauto.
simpl in |- *.
intro.
apply IHm.
tauto.
