Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma nc_B:forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let m0 := B m k x in nc m0 = nc m + if eqc_dec m0 x (A m k x) then 0 else 1.
Proof.
induction m.
unfold succ in |- *.
simpl in |- *.
tauto.
rename t into u.
unfold succ in |- *.
simpl in |- *.
intros.
decompose [and] H.
clear H.
unfold succ in IHm.
generalize (IHm k x H1 H0).
elim (eqc_dec (I (B m k x) d u p) x (A m k x)).
simpl in |- *.
unfold prec_I in H2.
intro.
elim a.
clear a.
intro.
absurd (x = d).
intro.
rewrite <- H3 in H2.
absurd (exd m x).
tauto.
apply succ_exd with k.
tauto.
unfold succ in |- *.
tauto.
tauto.
clear a.
intro.
elim (eqc_dec (B m k x) x (A m k x)).
intros.
omega.
tauto.
simpl in |- *.
intro.
elim (eqc_dec (B m k x) x (A m k x)).
tauto.
intros.
omega.
simpl in |- *.
unfold succ in |- *.
unfold prec_L in |- *.
simpl in |- *.
intros k x H.
decompose [and] H.
clear H.
rename d into j.
elim (eq_dim_dec j k).
intro.
elim (eq_dart_dec d0 x).
intros.
rewrite <- a0.
omega.
simpl in |- *.
intros.
unfold succ in IHm.
generalize (IHm k x H0 H).
intro.
elim (eqc_dec (L (B m k x) j d0 d1) x (A m k x)).
rewrite a.
simpl in |- *.
intro.
generalize H5.
clear H5.
elim (eqc_dec (B m k x) x (A m k x)).
intros.
assert (nc (B m k x) = nc m).
omega.
clear H5.
rewrite H7.
assert (eqc (B m k x) d0 d1 <-> eqc m d0 d1).
split.
apply eqc_B_eqc.
tauto.
unfold succ in |- *.
tauto.
apply eqc_eqc_B.
tauto.
unfold succ in |- *.
tauto.
tauto.
elim (eqc_dec (B m k x) d0 d1).
elim (eqc_dec m d0 d1).
intros.
clear a0 a1 a2 a3 H5.
omega.
intros.
generalize (eqc_dec (B m k x) d0 d1).
generalize (eqc_dec m d0 d1).
tauto.
intro.
elim (eqc_dec m d0 d1).
intro.
generalize (eqc_dec (B m k x) d0 d1).
generalize (eqc_dec m d0 d1).
tauto.
intro.
clear a0 a1 b0 b1 H5.
omega.
intros.
elim a0.
tauto.
clear a0.
intro.
elim H7.
clear H7.
intro.
elim (eqc_dec (B m k x) d0 d1).
intro.
elim b0.
apply eqc_trans with d0.
tauto.
apply eqc_trans with d1.
tauto.
tauto.
intro.
elim (eqc_dec m d0 d1).
intro.
omega.
intro.
generalize (eqc_B_CS m k x d0 d1).
unfold succ in |- *.
generalize (eqc_symm (B m k x) x d0).
generalize (eqc_symm (B m k x) d1 (A m k x)).
tauto.
clear H7.
intro.
elim (eqc_dec (B m k x) d0 d1).
intro.
elim b0.
apply eqc_trans with d1.
tauto.
apply eqc_trans with d0.
apply eqc_symm.
tauto.
tauto.
elim (eqc_dec m d0 d1).
intros.
clear b0 a0 b1 H7.
omega.
intros.
generalize (eqc_B_CS m k x d0 d1).
unfold succ in |- *.
tauto.
simpl in |- *.
intros.
generalize H5.
clear H5.
elim (eqc_dec (B m k x) x (A m k x)).
tauto.
intros.
elim (eqc_dec (B m k x) d0 d1).
intro.
elim (eqc_dec m d0 d1).
intro.
omega.
intro.
generalize (eqc_B_eqc m k x d0 d1).
unfold succ in |- *.
tauto.
intro.
elim (eqc_dec m d0 d1).
intro.
generalize (eqc_B_CN m k x d0 d1).
unfold succ in |- *.
intro.
generalize (eqc_symm (B m k x) d0 x).
generalize (eqc_symm (B m k x) (A m k x) d1).
tauto.
intro.
omega.
simpl in |- *.
intros.
unfold succ in IHm.
generalize (IHm k x H0 H).
intro.
elim (eqc_dec (L (B m k x) j d0 d1) x (A m k x)).
simpl in |- *.
intro.
generalize H5.
clear H5.
elim (eqc_dec (B m k x) x (A m k x)).
intros.
assert (nc (B m k x) = nc m).
omega.
clear H5.
rewrite H7.
assert (eqc (B m k x) d0 d1 <-> eqc m d0 d1).
split.
apply eqc_B_eqc.
tauto.
unfold succ in |- *.
tauto.
apply eqc_eqc_B.
tauto.
unfold succ in |- *.
tauto.
tauto.
elim (eqc_dec (B m k x) d0 d1).
elim (eqc_dec m d0 d1).
intros.
clear a1 a2 H5 a.
omega.
intros.
generalize (eqc_dec (B m k x) d0 d1).
generalize (eqc_dec m d0 d1).
tauto.
intro.
elim (eqc_dec m d0 d1).
intro.
generalize (eqc_dec (B m k x) d0 d1).
generalize (eqc_dec m d0 d1).
tauto.
intro.
clear a0 b0 b1 H5 a.
omega.
intros.
elim a.
tauto.
clear a.
intro.
elim H7.
clear H7.
intro.
elim (eqc_dec (B m k x) d0 d1).
intro.
elim b0.
apply eqc_trans with d0.
tauto.
apply eqc_trans with d1.
tauto.
tauto.
intro.
elim (eqc_dec m d0 d1).
intro.
clear b0 b1 H7 a.
omega.
intro.
generalize (eqc_B_CS m k x d0 d1).
unfold succ in |- *.
generalize (eqc_symm (B m k x) x d0).
generalize (eqc_symm (B m k x) d1 (A m k x)).
tauto.
clear H7.
intro.
elim (eqc_dec (B m k x) d0 d1).
intro.
elim b0.
apply eqc_trans with d1.
tauto.
apply eqc_trans with d0.
apply eqc_symm.
tauto.
tauto.
elim (eqc_dec m d0 d1).
intros.
omega.
intros.
generalize (eqc_B_CS m k x d0 d1).
unfold succ in |- *.
tauto.
simpl in |- *.
intros.
generalize H5.
clear H5.
elim (eqc_dec (B m k x) x (A m k x)).
tauto.
intros.
elim (eqc_dec (B m k x) d0 d1).
intro.
elim (eqc_dec m d0 d1).
intro.
omega.
intro.
generalize (eqc_B_eqc m k x d0 d1).
unfold succ in |- *.
tauto.
intro.
elim (eqc_dec m d0 d1).
intro.
generalize (eqc_B_CN m k x d0 d1).
unfold succ in |- *.
intro.
generalize (eqc_symm (B m k x) d0 x).
generalize (eqc_symm (B m k x) (A m k x) d1).
tauto.
intro.
omega.
