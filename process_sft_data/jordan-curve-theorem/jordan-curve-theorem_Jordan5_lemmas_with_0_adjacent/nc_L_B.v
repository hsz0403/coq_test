Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma nc_L_B:forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let m0:= B m k x in let m1:= L m0 k x (A m k x) in nc m1 = nc m.
Proof.
simpl in |- *.
intros.
generalize (nc_B m k x).
simpl in |- *.
intros.
assert (nc (B m k x) = nc m + (if eqc_dec (B m k x) x (A m k x) then 0 else 1)).
tauto.
omega.
