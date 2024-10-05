Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma ndZ_B:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> nd (B m k x) = nd m.
Proof.
intros.
simpl in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold succ in |- *.
simpl in |- *.
intros.
unfold succ in IHm.
unfold succ in H0.
simpl in H0.
assert (nd (B m k x) = nd m).
apply IHm.
simpl in H.
tauto.
tauto.
omega.
simpl in |- *.
unfold succ in H0.
simpl in H0.
generalize H0.
clear H0.
simpl in H.
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
