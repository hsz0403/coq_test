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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma nc_L_B:forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let m0:= B m k x in let m1:= L m0 k x (A m k x) in nc m1 = nc m.
Proof.
simpl in |- *.
intros.
generalize (nc_B m k x).
simpl in |- *.
intros.
assert (nc (B m k x) = nc m + (if eqc_dec (B m k x) x (A m k x) then 0 else 1)).
tauto.
Admitted.

Lemma A_not_cA: forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> A m k x <> cA (B m k x) k x.
Proof.
intros.
generalize (succ_bottom m k x H H0).
intro.
assert (exd m x).
apply succ_exd with k.
tauto.
tauto.
generalize (cA_B m k x x H H0).
elim (eq_dart_dec x x).
intros.
rewrite H3.
intro.
symmetry in H4.
tauto.
Admitted.

Lemma nf_L_B_aux :forall(m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> let y := A m k x in let m0 := B m k x in let m1 := L m0 k x (A m k x) in nf m1 = match k with | zero => let x_1 := cA_1 m0 one x in nf m0 + (if expf_dec m0 x_1 y then 1 else -1) | one => let y0 := cA m0 zero y in nf m0 + (if expf_dec m0 x y0 then 1 else -1) end.
Proof.
simpl in |- *.
Admitted.

Lemma cA_I:forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> x <> z -> (cA (I m x u p) k z = cA m k z).
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
tauto.
Admitted.

Lemma cA_1_I:forall(m:fmap)(k:dim)(x z:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> x <> z -> (cA_1 (I m x u p) k z = cA_1 m k z).
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x z).
tauto.
Admitted.

Lemma expf_refl: forall(m:fmap)(z:dart), inv_hmap m -> exd m z -> expf m z z.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
Admitted.

Lemma ne_B:forall (m:fmap)(k:dim)(x:dart), inv_hmap m -> succ m k x -> ne (B m k x) = ne m + if (eq_dim_dec k zero) then 1 else 0.
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
assert (ne (B m k x) = ne m + (if eq_dim_dec k zero then 1 else 0)).
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
induction k.
simpl in |- *.
elim (eq_dim_dec d zero).
elim (eq_dart_dec d0 x).
intros.
induction d.
omega.
inversion a0.
simpl in |- *.
intros.
induction d.
unfold succ in IHm.
assert (ne (B m zero x) = ne m + (if eq_dim_dec zero zero then 1 else 0)).
apply IHm.
tauto.
tauto.
generalize H1.
clear H1.
elim (eq_dim_dec zero zero).
intros.
omega.
tauto.
inversion a.
simpl in |- *.
induction d.
tauto.
intros.
assert (ne (B m zero x) = ne m + (if eq_dim_dec zero zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
clear H1.
elim (eq_dim_dec zero zero).
tauto.
tauto.
simpl in |- *.
elim (eq_dim_dec d one).
elim (eq_dart_dec d0 x).
elim d.
intros.
inversion a0.
intros.
omega.
simpl in |- *.
intros.
elim d.
assert (ne (B m one x) = ne m + (if eq_dim_dec one zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
elim (eq_dim_dec one zero).
intro.
inversion a0.
intros.
omega.
assert (ne (B m one x) = ne m + (if eq_dim_dec one zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
elim (eq_dim_dec one zero).
intro.
inversion a0.
tauto.
simpl in |- *.
intros.
elim d.
assert (ne (B m one x) = ne m + (if eq_dim_dec one zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
elim (eq_dim_dec one zero).
intro.
inversion a.
intros.
omega.
assert (ne (B m one x) = ne m + (if eq_dim_dec one zero then 1 else 0)).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
generalize H1.
elim (eq_dim_dec one zero).
intro.
inversion a.
intros.
omega.
