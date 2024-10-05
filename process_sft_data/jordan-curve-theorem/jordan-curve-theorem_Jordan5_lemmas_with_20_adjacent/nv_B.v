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

Lemma expf_symm:forall(m:fmap)(z t:dart), expf m z t -> expf m t z.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
Admitted.

Lemma expf_trans:forall (m : fmap) (z t u : dart), expf m z t -> expf m t u -> expf m z u.
Proof.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with t.
tauto.
Admitted.

Lemma cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> (cF (I m x u p) z = cF m z).
Proof.
unfold cF in |- *.
intros.
rewrite cA_1_I.
rewrite cA_1_I.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
simpl in |- *.
elim (eq_dart_dec x z).
tauto.
intro.
intro.
unfold prec_I in H0.
generalize (exd_cA_1 m zero z).
rewrite <- H3.
Admitted.

Lemma Iter_cF_I:forall(m:fmap)(x z:dart)(u:tag)(p:point)(i:nat), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> Iter (cF (I m x u p)) i z = Iter (cF m) i z.
Proof.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
intros.
rewrite IHi.
rewrite cF_I.
tauto.
tauto.
tauto.
assert (MF.f = cF).
tauto.
rewrite <- H3.
generalize (MF.exd_Iter_f m i z).
tauto.
intro.
unfold prec_I in H0.
rewrite H3 in H0.
generalize (MF.exd_Iter_f m i z).
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma expf_I:forall(m:fmap)(x z t:dart)(u:tag)(p:point), inv_hmap m -> prec_I m x -> exd m z -> x <> z -> (expf (I m x u p) z t <-> expf m z t).
Proof.
intros.
unfold expf in |- *.
unfold MF.expo in |- *.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H3.
split.
intros.
decompose [and] H4.
clear H4.
elim H9.
intros i Eq.
split.
tauto.
split.
tauto.
split with i.
generalize (Iter_cF_I m x z u p i H7 H8 H1 H2).
intro.
rewrite <- H4.
tauto.
intros.
decompose [and] H4.
clear H4.
split.
tauto.
split.
tauto.
elim H8.
intros i Hi.
split with i.
rewrite Iter_cF_I.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma cF_L:forall(m:fmap)(k:dim)(x y z:dart), inv_hmap m -> prec_L m k x y -> cF (L m k x y) z = if eq_dim_dec k zero then cA_1 m one (if eq_dart_dec y z then x else if eq_dart_dec (cA m zero x) z then cA_1 m zero y else cA_1 m zero z) else (if eq_dart_dec y (cA_1 m zero z) then x else if eq_dart_dec (cA m one x) (cA_1 m zero z) then cA_1 m one y else cA_1 m one (cA_1 m zero z)).
Proof.
unfold cF in |- *.
intros.
simpl in |- *.
elim (eq_dim_dec k zero).
intro.
elim (eq_dim_dec k one).
intro.
rewrite a0 in a.
inversion a.
tauto.
intro.
elim (eq_dim_dec k one).
tauto.
intro.
induction k.
tauto.
Admitted.

Lemma expf_L0_y_x_1:forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in expf (L m zero x y) y x_1.
Proof.
intros.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
simpl in H.
unfold prec_L in H.
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H0.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y y).
unfold x_1 in |- *.
tauto.
tauto.
tauto.
simpl in H.
tauto.
simpl in H.
Admitted.

Lemma expf_L0_x0_y_0_1:forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x0 := cA m zero x in let y_0_1 := cF m y in expf (L m zero x y) x0 y_0_1.
Proof.
intros.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
simpl in H.
unfold prec_L in H.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H0.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y x0).
intros.
simpl in H.
unfold prec_L in H.
symmetry in a.
fold x0 in H.
tauto.
elim (eq_dart_dec (cA m zero x) x0).
intros.
unfold y_0_1 in |- *.
unfold cF in |- *.
tauto.
fold x0 in |- *.
tauto.
tauto.
simpl in H.
tauto.
simpl in H.
Admitted.

Lemma cF_L0_1:forall (m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in betweenf m x_1 z y -> cF (L m zero x y) z = if eq_dart_dec y z then x_1 else cF m z.
Proof.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
assert (exd m (cA_1 m one x)).
generalize (exd_cA_1 m one x).
tauto.
generalize (H0 H1 H).
clear H0.
intro.
elim H0.
intros i Hi.
clear H0.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
clear Hj.
assert (MF.f = cF).
tauto.
rewrite H9 in H0.
rewrite H9 in H8.
rewrite cF_L.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec y z).
tauto.
elim (eq_dart_dec (cA m zero x) z).
intros.
set (p := MF.Iter_upb m (cA_1 m one x)) in |- *.
fold p in H10.
assert (z = Iter (cF m) (p - 1) (cA_1 m one x)).
assert (cF m z = cA_1 m one x).
unfold cF in |- *.
rewrite <- a0.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
assert (z = cF_1 m (cA_1 m one x)).
rewrite <- H11.
rewrite cF_1_cF.
tauto.
tauto.
rewrite <- a0.
generalize (exd_cA m zero x).
tauto.
rewrite H12.
assert (cA_1 m one x = cF m (Iter (cF m) (p - 1) (cA_1 m one x))).
rewrite <- H9.
assert (MF.f m (Iter (MF.f m) (p - 1) (cA_1 m one x)) = Iter (MF.f m) p (cA_1 m one x)).
assert (p = S (p - 1)).
omega.
rewrite H13.
simpl in |- *.
assert ((p - 1 - 0)%nat = (p - 1)%nat).
omega.
rewrite H14.
tauto.
rewrite H13.
unfold p in |- *.
set (x_1 := cA_1 m one x) in |- *.
generalize (MF.Iter_upb_period m x_1).
simpl in |- *.
intros.
rewrite H14.
tauto.
tauto.
unfold x_1 in |- *.
tauto.
rewrite H13.
rewrite cF_1_cF.
rewrite <- H13.
tauto.
tauto.
generalize (MF.exd_Iter_f m (p - 1) (cA_1 m one x)).
tauto.
assert (i = (p - 1)%nat).
eapply (MF.unicity_mod_p m (cA_1 m one x)).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H9.
rewrite <- H11.
tauto.
assert (i = j).
omega.
rewrite H13 in H0.
rewrite H8 in H0.
tauto.
unfold cF in |- *.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
Admitted.

Lemma cF_L0_2:forall (m:fmap)(x y z:dart), inv_hmap (L m zero x y) -> let y_0_1 := cF m y in let x0 := cA m zero x in betweenf m y_0_1 z x0 -> cF (L m zero x y) z = if eq_dart_dec x0 z then y_0_1 else cF m z.
Proof.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H.
clear H.
assert (exd m (cF m y)).
generalize (exd_cF m y).
tauto.
generalize (H0 H1 H).
clear H0.
intro.
elim H0.
intros i Hi.
clear H0.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
clear Hj.
assert (MF.f = cF).
tauto.
rewrite H9 in H0.
rewrite H9 in H8.
rewrite cF_L in |- *.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec y z).
intro.
elim (eq_dart_dec (cA m zero x) z).
rewrite a0 in H7.
tauto.
intro.
set (p := MF.Iter_upb m (cF m y)) in |- *.
fold p in H10.
assert (cF m y = Iter (cF m) p (cF m y)).
rewrite <- H9 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
rewrite H9 in |- *.
tauto.
assert (z = Iter (cF m) (p - 1) (cF m y)).
rewrite <- a0 in |- *.
assert (p = S (p - 1)).
omega.
rewrite H12 in H11.
simpl in H11.
assert (inj_dart (exd m) (cF m)).
apply inj_cF.
tauto.
unfold inj_dart in H13.
apply H13.
tauto.
generalize (MF.exd_Iter_f m (p - 1) (cF m y)).
tauto.
tauto.
assert (j = (j - i + i)%nat).
omega.
generalize H8.
rewrite H13 in |- *.
rewrite <- H9 in |- *.
rewrite MF.Iter_comp in |- *.
rewrite H9 in |- *.
rewrite H0 in |- *.
intro.
assert ((p - 1)%nat = (p - 1 - j + j)%nat).
omega.
generalize H12.
rewrite H15 in |- *.
rewrite <- H9 in |- *.
rewrite MF.Iter_comp in |- *.
rewrite H9 in |- *.
rewrite H8 in |- *.
rewrite <- H14 in |- *.
rewrite <- H9 in |- *.
rewrite <- MF.Iter_comp in |- *.
intro.
assert (p = MF.Iter_upb m z).
rewrite <- H0 in |- *.
unfold p in |- *.
apply MF.period_uniform.
tauto.
tauto.
clear H13.
clear a.
clear H15.
assert ((p - 1 - j + (j - i))%nat = (p - 1 - i)%nat).
omega.
rewrite H13 in H16.
clear H13.
assert (0%nat = (p - 1 - i)%nat).
apply (MF.unicity_mod_p m z 0 (p - 1 - i)).
tauto.
rewrite <- a0 in |- *.
tauto.
rewrite <- H17 in |- *.
omega.
rewrite <- H17 in |- *.
omega.
rewrite <- H16 in |- *.
simpl in |- *.
tauto.
assert (i = j).
omega.
rewrite H15 in H0.
rewrite <- a0 in H0.
rewrite H8 in H0.
tauto.
elim (eq_dart_dec (cA m zero x) z).
unfold cF in |- *.
tauto.
unfold cF in |- *.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
Admitted.

Lemma between_expf_L0_1:forall (m:fmap)(x y:dart)(i:nat), inv_hmap (L m zero x y) -> let x_1 := cA_1 m one x in let z := Iter (cF m) i x_1 in betweenf m x_1 z y -> expf (L m zero x y) x_1 z.
Proof.
intros.
induction i.
assert (z = x_1).
unfold z in |- *.
simpl in |- *.
tauto.
rewrite H1.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
simpl in |- *.
simpl in H.
unfold prec_L in H.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
simpl in z.
generalize H0.
clear H0.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
intro.
simpl in H.
unfold prec_L in H.
decompose [and] H.
clear H.
assert (exd m (cA_1 m one x)).
generalize (exd_cA_1 m one x).
tauto.
generalize (H0 H1 H).
clear H0.
intro.
elim H0.
clear H0.
intros k Hk.
elim Hk.
intros j Hj.
decompose [and] Hj.
clear Hj.
clear Hk.
assert (MF.f = cF).
tauto.
rewrite H9 in H0.
rewrite H9 in H8.
induction k.
simpl in H0.
rewrite <- H0.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
apply MF.expo_refl.
simpl in |- *.
tauto.
simpl in H0.
assert (cF_1 m z = Iter (cF m) i x_1).
unfold z in |- *.
rewrite cF_1_cF.
tauto.
tauto.
rewrite <- H9.
generalize (MF.exd_Iter_f m i x_1).
tauto.
rewrite <- H0 in H11.
rewrite cF_1_cF in H11.
assert (z = cF m (Iter (cF m) k x_1)).
rewrite H11.
unfold z in |- *.
tauto.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
apply MF.expo_trans with (Iter (cF m) k x_1).
simpl in IHi.
unfold expf in IHi.
rewrite <- H11 in IHi.
assert (betweenf m x_1 (Iter (cF m) k x_1) y).
unfold betweenf in |- *.
unfold MF.between in |- *.
fold x_1 in H.
intros.
clear H14 H13.
split with k.
split with j.
split.
rewrite H9.
tauto.
split.
tauto.
omega.
tauto.
rewrite <- H0.
assert (cF (L m zero x y) (Iter (cF m) k x_1) = cF m (Iter (cF m) k x_1)).
rewrite cF_L0_1.
elim (eq_dart_dec y (Iter (cF m) k x_1)).
intro.
rewrite a in H8.
assert (j = k).
apply (MF.unicity_mod_p m x_1 j k H1).
unfold x_1 in |- *.
tauto.
tauto.
omega.
rewrite H9.
tauto.
absurd (j = k).
omega.
tauto.
tauto.
simpl in |- *.
unfold prec_L in |- *.
tauto.
fold x_1 in |- *.
unfold betweenf in |- *.
unfold MF.between in |- *.
fold x_1 in H.
intros.
clear H14 H13.
split with k.
split with j.
split.
rewrite H9.
tauto.
split.
tauto.
omega.
rewrite <- H13.
rewrite <- H9.
unfold MF.expo in |- *.
split.
simpl in |- *.
generalize (MF.exd_Iter_f m k x_1).
unfold x_1 in |- *.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
tauto.
rewrite <- H9.
generalize (MF.exd_Iter_f m k x_1).
unfold x_1 in |- *.
Admitted.

Lemma between_expf_L0_2:forall (m:fmap)(x y:dart)(i:nat), inv_hmap (L m zero x y) -> let y_0_1 := cF m y in let x0 := cA m zero x in let z := Iter (cF m) i y_0_1 in betweenf m y_0_1 z x0 -> expf (L m zero x y) y_0_1 z.
Proof.
intros.
induction i.
simpl in z.
unfold z in |- *.
unfold z in H0.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
simpl in |- *.
simpl in H.
unfold prec_L in H.
unfold y_0_1 in |- *.
generalize (exd_cF m y).
tauto.
generalize H0.
clear H0.
unfold betweenf in |- *.
unfold MF.between in |- *.
simpl in |- *.
intro.
simpl in H.
unfold prec_L in H.
decompose [and] H.
clear H.
assert (exd m (cA_1 m zero y)).
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
unfold cF in |- *.
generalize (exd_cA_1 m one (cA_1 m zero y)).
tauto.
generalize (H0 H1 H6).
clear H0.
intro.
elim H0.
clear H0.
intros k Hk.
elim Hk.
intros j Hj.
decompose [and] Hj.
clear Hj.
clear Hk.
assert (MF.f = cF).
tauto.
rewrite H10 in H0.
rewrite H10 in H9.
induction k.
simpl in H0.
rewrite <- H0 in |- *.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
apply MF.expo_refl.
simpl in |- *.
tauto.
simpl in H0.
set (z_1 := cF_1 m z) in |- *.
assert (z_1 = Iter (cF m) i y_0_1).
unfold z_1 in |- *.
unfold z in |- *.
simpl in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (MF.exd_Iter_f m i y_0_1).
tauto.
assert (z_1 = Iter (cF m) k y_0_1).
unfold z_1 in |- *.
rewrite <- H0 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
rewrite <- H10 in |- *.
generalize (MF.exd_Iter_f m k y_0_1).
tauto.
apply expf_trans with z_1.
rewrite <- H12 in IHi.
apply IHi.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear H14 H15.
split with k.
split with j.
split.
symmetry in |- *.
rewrite H10 in |- *.
tauto.
split.
rewrite H10 in |- *.
tauto.
omega.
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
rewrite H12 in |- *.
generalize (MF.exd_Iter_f m i y_0_1).
rewrite H10 in |- *.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H10 in |- *.
unfold cF in |- *.
simpl in |- *.
elim (eq_dart_dec y z_1).
intro.
assert (z = cF m z_1).
unfold z_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold z in |- *.
generalize (MF.exd_Iter_f m (S i) y_0_1).
rewrite H10 in |- *.
tauto.
assert (z = y_0_1).
unfold y_0_1 in |- *.
rewrite a in |- *.
unfold z_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold z in |- *.
generalize (MF.exd_Iter_f m (S i) y_0_1).
rewrite H10 in |- *.
tauto.
assert (S k = 0%nat).
apply (MF.unicity_mod_p m y_0_1 (S k) 0 H1 H6).
omega.
omega.
simpl in |- *.
rewrite H10 in |- *.
rewrite H0 in |- *.
tauto.
inversion H16.
elim (eq_dart_dec (cA m zero x) z_1).
intros.
assert (k = j).
apply (MF.unicity_mod_p m y_0_1 k j H1 H6).
omega.
tauto.
rewrite H10 in |- *.
rewrite H9 in |- *.
rewrite <- H13 in |- *.
symmetry in |- *.
unfold x0 in |- *.
tauto.
absurd (k = j).
omega.
tauto.
intros.
fold (cF m z_1) in |- *.
unfold z_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold z in |- *.
generalize (MF.exd_Iter_f m (S i) y_0_1).
rewrite H10 in |- *.
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
omega.
