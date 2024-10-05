Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma ne_L_B:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let m1 := L (B m k x) k x (A m k x) in ne m1 = ne m.
Proof.
simpl in |- *.
intros.
generalize (ne_B m k x H H0).
induction k.
elim (eq_dim_dec zero zero).
intros.
omega.
tauto.
elim (eq_dim_dec one zero).
intro.
inversion a.
intros.
omega.
