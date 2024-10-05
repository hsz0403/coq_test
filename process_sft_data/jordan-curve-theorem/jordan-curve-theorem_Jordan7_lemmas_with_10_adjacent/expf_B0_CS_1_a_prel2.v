Require Export Jordan6.

Lemma cF_B:forall(m:fmap)(k:dim)(x z:dart), inv_hmap m -> succ m k x -> cF (B m k x) z = if eq_dim_dec k zero then cA_1 (B m zero x) one (if eq_dart_dec (A m zero x) z then top m zero x else if eq_dart_dec (bottom m zero x) z then x else cA_1 m zero z) else (if eq_dart_dec (A m one x) (cA_1 (B m one x) zero z) then top m one x else if eq_dart_dec (bottom m one x) (cA_1 (B m one x) zero z) then x else cA_1 m one (cA_1 (B m one x) zero z)).
Proof.
intros.
unfold cF in |- *.
elim (eq_dim_dec k zero).
intro.
rewrite a.
rewrite cA_1_B.
tauto.
tauto.
rewrite a in H0.
tauto.
intro.
induction k.
tauto.
rewrite cA_1_B.
tauto.
tauto.
Admitted.

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
Admitted.

Lemma expf_B0_CS_1_a_prel1:forall (m:fmap)(x:dart)(i j:nat), inv_hmap m -> succ m zero x -> let x_1 := cA_1 m one x in let p := MF.Iter_upb m x_1 in let xb0 := bottom m zero x in let z := Iter (cF m) i x_1 in xb0 = Iter (cF m) j x_1 -> (i <= j < p)%nat -> expf (B m zero x) x_1 z.
Proof.
intros.
unfold betweenf in |- *.
unfold MF.between in |- *.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
unfold expf in |- *.
split.
apply inv_hmap_B.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_B m zero x x_1).
tauto.
split with i.
assert (MF.f = cF).
tauto.
rewrite H5.
induction i.
simpl in |- *.
simpl in z.
unfold z in |- *.
tauto.
simpl in |- *.
simpl in z.
simpl in IHi.
rewrite IHi.
set (zi := Iter (cF m) i x_1) in |- *.
fold zi in z.
rewrite cF_B.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec (A m zero x) zi).
intro.
set (x0 := A m zero x) in |- *.
fold x0 in a0.
assert (cF m x0 = x_1).
assert (cA m zero x = x0).
unfold x0 in |- *.
rewrite (A_cA m zero x x0).
unfold x0 in |- *; tauto.
tauto.
tauto.
unfold x0 in |- *.
apply succ_exd_A.
tauto.
tauto.
unfold x0 in |- *.
tauto.
rewrite <- H6.
unfold x_1 in |- *.
unfold cF in |- *.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
assert (x_1 = Iter (cF m) p x_1).
unfold p in |- *.
rewrite MF.Iter_upb_period.
tauto.
tauto.
tauto.
assert (cF_1 m x_1 = cF_1 m (Iter (cF m) p x_1)).
rewrite <- H7.
tauto.
assert (p = S (p - 1)).
omega.
rewrite H9 in H8.
rewrite MF.f_1_Iter_f in H8.
assert (cF_1 m x_1 = x0).
rewrite <- H6.
rewrite cF_1_cF.
tauto.
tauto.
unfold x0 in |- *.
apply succ_exd_A.
tauto.
tauto.
rewrite H10 in H8.
assert (i = (p - 1)%nat).
apply (MF.unicity_mod_p m x_1).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite <- H8.
rewrite H5.
fold zi in |- *.
symmetry in |- *.
tauto.
absurd (i = (p - 1)%nat).
omega.
tauto.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m zero x) zi).
intro.
assert (i = j).
apply (MF.unicity_mod_p m x_1 i j).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H5.
fold zi in |- *.
rewrite <- H1.
unfold xb0 in |- *.
symmetry in |- *.
tauto.
absurd (i = j).
omega.
tauto.
intro.
rewrite cA_1_B_ter.
unfold z in |- *.
unfold cF in |- *.
tauto.
tauto.
intro.
inversion H6.
tauto.
tauto.
tauto.
Admitted.

Lemma expf_B0_CS_1_a_aux:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> exd m z -> exd m t -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in expf m x0 xb0 -> (betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0) -> expf (B m zero x) z t.
Proof.
intros.
assert (expf (B m zero x) x_1 z).
unfold x_1 in |- *.
apply expf_B0_CS_1_a_prel2.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xb0 in |- *.
tauto.
assert (expf (B m zero x) x_1 t).
unfold x_1 in |- *.
apply expf_B0_CS_1_a_prel2.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xb0 in |- *.
tauto.
generalize H5 H6.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with x_1.
apply MF.expo_symm.
tauto.
tauto.
Admitted.

Lemma expf_B0_CS_1_a:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in expf m x0 xb0 -> (betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0) -> expf (B m zero x) z t.
Proof.
intros.
assert (exd m z /\ exd m t).
unfold betweenf in H2.
unfold MF.between in H2.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
elim H2.
clear H2.
intros.
elim H2.
intros i Hi.
elim Hi.
intros j Hj.
clear Hi.
clear H2.
elim Hj.
clear Hj.
intros.
assert (exd m z).
rewrite <- H2 in |- *.
generalize (MF.exd_Iter_f m i x_1).
tauto.
elim H5.
intros k Hk.
clear H5.
elim Hk.
clear Hk.
intros l Hl.
elim Hl.
clear Hl.
intros.
assert (exd m t).
rewrite <- H5 in |- *.
generalize (MF.exd_Iter_f m k x_1).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
apply expf_B0_CS_1_a_aux.
tauto.
tauto.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xb0 in |- *.
Admitted.

Lemma expf_B0_CS_1_b_prel1:forall (m:fmap)(x:dart)(i j:nat), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in let p := MF.Iter_upb m xh0_1 in let z := Iter (cF m) i xh0_1 in x0 = Iter (cF m) j xh0_1 -> (i <= j < p)%nat -> expf (B m zero x) xh0_1 z.
Proof.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m xh0).
unfold xh0 in |- *.
apply exd_top.
tauto.
tauto.
assert (exd m xh0_1).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
tauto.
unfold expf in |- *.
split.
apply inv_hmap_B.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_B m zero x xh0_1).
tauto.
split with i.
assert (MF.f = cF).
tauto.
rewrite H6 in |- *.
induction i.
simpl in |- *.
simpl in z.
unfold z in |- *.
tauto.
simpl in |- *.
simpl in z.
simpl in IHi.
rewrite IHi in |- *.
set (zi := Iter (cF m) i xh0_1) in |- *.
fold zi in z.
rewrite cF_B in |- *.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec (A m zero x) zi).
intro.
fold xh0 in |- *.
assert (zi = x0).
rewrite <- a0 in |- *.
unfold x0 in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
assert (i = j).
apply (MF.unicity_mod_p m xh0_1).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H6 in |- *.
fold zi in |- *.
rewrite <- H1 in |- *.
tauto.
absurd (i = j).
omega.
tauto.
intro.
elim (eq_dart_dec (bottom m zero x) zi).
intro.
assert (xh0 = cA_1 m zero xb0).
unfold xb0 in |- *.
rewrite cA_1_bottom in |- *.
fold xh0 in |- *.
tauto.
tauto.
tauto.
assert (xh0_1 = z).
unfold xh0_1 in |- *.
unfold z in |- *.
unfold cF in |- *.
rewrite H7 in |- *.
fold xb0 in a0.
rewrite a0 in |- *.
tauto.
assert (xh0_1 = Iter (cF m) 0 xh0_1).
simpl in |- *.
tauto.
assert (z = Iter (cF m) (S i) xh0_1).
simpl in |- *.
fold zi in |- *.
fold z in |- *.
tauto.
assert (0%nat = S i).
apply (MF.unicity_mod_p m xh0_1).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H6 in |- *.
rewrite <- H9 in |- *.
rewrite <- H10 in |- *.
tauto.
inversion H11.
intro.
rewrite cA_1_B_ter in |- *.
fold (cF m zi) in |- *.
fold z in |- *.
tauto.
tauto.
intro.
inversion H7.
tauto.
tauto.
tauto.
Admitted.

Lemma expf_B0_CS_1_b_prel2:forall (m:fmap)(x z:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in expf m x0 xb0 -> betweenf m xh0_1 z x0 -> expf (B m zero x) xh0_1 z.
Proof.
intros.
generalize H2.
clear H2.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim H2.
clear H2.
intros i Hi.
elim Hi.
clear Hi.
intros j Hj.
unfold xh0_1 in |- *.
decompose [and] Hj.
clear Hj.
rewrite <- H2 in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply (expf_B0_CS_1_b_prel1 m x i j).
tauto.
tauto.
fold xb0 in |- *.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold x0 in |- *; symmetry in |- *.
tauto.
fold xh0 in |- *; fold xh0_1 in |- *.
omega.
tauto.
assert (exd m xh0).
unfold xh0 in |- *.
apply exd_top.
tauto.
apply succ_exd with zero.
tauto.
tauto.
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
Admitted.

Lemma expf_B0_CS_1_b_aux:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> exd m z -> exd m t -> let x0 := cA m zero x in let xb0 := bottom m zero x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in expf m x0 xb0 -> (betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0) -> expf (B m zero x) z t.
Proof.
intros.
assert (expf (B m zero x) xh0_1 z).
unfold xh0_1 in |- *; unfold xh0 in |- *.
apply expf_B0_CS_1_b_prel2.
tauto.
tauto.
fold xb0 in |- *; fold x0 in |- *.
tauto.
fold x0 in |- *; fold xh0 in |- *; fold xh0_1 in |- *.
tauto.
assert (expf (B m zero x) xh0_1 t).
unfold xh0_1 in |- *; unfold xh0 in |- *.
apply expf_B0_CS_1_b_prel2.
tauto.
tauto.
fold xb0 in |- *; fold x0 in |- *.
tauto.
fold x0 in |- *; fold xh0 in |- *; fold xh0_1 in |- *.
tauto.
apply expf_trans with xh0_1.
apply expf_symm.
tauto.
Admitted.

Lemma expf_B0_CS_1_b:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in expf m x0 xb0 -> (betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0) -> expf (B m zero x) z t.
Proof.
intros.
assert (exd m z /\ exd m t).
unfold betweenf in H2.
unfold MF.between in H2.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m xh0).
unfold xh0 in |- *.
apply exd_top.
tauto.
apply succ_exd with zero.
tauto.
tauto.
assert (exd m xh0_1).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
tauto.
elim H2.
clear H2.
intros.
elim H2.
intros i Hi.
elim Hi.
intros j Hj.
clear Hi.
clear H2.
elim Hj.
clear Hj.
intros.
assert (exd m z).
rewrite <- H2 in |- *.
generalize (MF.exd_Iter_f m i xh0_1).
tauto.
elim H6.
intros k Hk.
clear H6.
elim Hk.
clear Hk.
intros l Hl.
elim Hl.
clear Hl.
intros.
assert (exd m t).
rewrite <- H6 in |- *.
generalize (MF.exd_Iter_f m k xh0_1).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
apply expf_B0_CS_1_b_aux.
tauto.
tauto.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xb0 in |- *.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold x0 in |- *.
Admitted.

Lemma expf_B0_CS_1_c_prel:forall (m:fmap)(x z:dart)(i:nat), inv_hmap m -> succ m zero x -> exd m z -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in let t:= Iter (cF m) i z in expf m x0 xb0 -> ~ expf m x_1 z -> expf (B m zero x) z t.
Proof.
intros.
induction i.
simpl in t.
unfold t in |- *.
unfold expf in |- *.
split.
apply inv_hmap_B.
tauto.
apply MF.expo_refl.
generalize (exd_B m zero x z).
tauto.
unfold t in |- *.
simpl in |- *.
unfold expf in |- *.
split.
apply inv_hmap_B.
tauto.
simpl in IHi.
unfold expf in IHi.
elim IHi.
clear IHi.
intros.
eapply MF.expo_trans.
apply H5.
set (zi := Iter (cF m) i z) in |- *.
unfold MF.expo in |- *.
split.
assert (exd m zi).
unfold zi in |- *.
assert (cF = MF.f).
tauto.
rewrite H6 in |- *.
generalize (MF.exd_Iter_f m i z).
tauto.
generalize (exd_B m zero x zi).
tauto.
split with 1%nat.
simpl in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H6 in |- *.
rewrite cF_B in |- *.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec (A m zero x) zi).
intros.
clear a0.
assert (x = A_1 m zero zi).
rewrite <- a in |- *.
rewrite A_1_A in |- *.
tauto.
tauto.
tauto.
unfold x_1 in H3.
rewrite H7 in H3.
assert (cA_1 m zero zi = A_1 m zero zi).
rewrite cA_1_eq in |- *.
assert (pred m zero zi).
unfold pred in |- *.
rewrite <- H7 in |- *.
apply exd_not_nil with m.
tauto.
apply succ_exd with zero.
tauto.
tauto.
elim (pred_dec m zero zi).
tauto.
tauto.
tauto.
rewrite <- H8 in H3.
elim H3.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
fold (cF m zi) in |- *.
rewrite H6 in |- *.
unfold MF.expo in |- *.
split.
tauto.
split with (S i).
simpl in |- *.
rewrite <- H6 in |- *.
fold zi in |- *.
tauto.
elim (eq_dart_dec (bottom m zero x) zi).
intros.
fold xb0 in a.
rewrite a in H2.
elim H3.
generalize H2.
clear H2.
unfold expf in |- *.
clear a0.
split.
tauto.
decompose [and] H2.
clear H2.
clear H7.
apply MF.expo_symm.
tauto.
apply MF.expo_trans with zi.
unfold zi in |- *.
rewrite H6 in |- *.
unfold MF.expo in |- *.
split.
tauto.
split with i.
tauto.
apply MF.expo_trans with x0.
apply MF.expo_symm.
tauto.
tauto.
unfold x0 in |- *.
unfold x_1 in |- *.
fold x0 in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
rewrite H2 in |- *.
fold (cF m x0) in |- *.
rewrite H6 in |- *.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
intros.
rewrite cA_1_B_ter in |- *.
unfold cF in |- *.
tauto.
tauto.
intro.
inversion H7.
tauto.
tauto.
Admitted.

Lemma expf_B0_CS_1_c:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in expf m x0 xb0 -> (~ expf m x_1 z /\ expf m z t) -> expf (B m zero x) z t.
Proof.
intros.
decompose [and] H2.
clear H2.
unfold expf in H4.
unfold MF.expo in H4.
decompose [and] H4.
clear H4.
elim H7.
intros i Hi; clear H7.
rewrite <- Hi in |- *.
apply expf_B0_CS_1_c_prel.
tauto.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold x_1 in |- *.
Admitted.

Lemma expf_B0_CS_1:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in expf m x0 xb0 -> (betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0 \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t) -> expf (B m zero x) z t.
Proof.
intros.
elim H2.
clear H2.
intro.
apply expf_B0_CS_1_a.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xb0 in |- *.
tauto.
clear H2.
intro.
elim H2.
clear H2.
intro.
apply expf_B0_CS_1_b.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold x0 in |- *.
tauto.
clear H2.
intro.
apply expf_B0_CS_1_c.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
Admitted.

Lemma between_expf_B0_1:forall (m:fmap)(x:dart)(i:nat), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let p:= MF.Iter_upb m x_1 in let z:= Iter (cF m) i x_1 in ~expf m x0 xb0 -> (i < p)%nat -> expf (B m zero x) x_1 z.
Proof.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
induction i.
simpl in z.
unfold z in |- *.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
generalize (exd_B m zero x x_1).
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with (Iter (cF m) i x_1).
simpl in IHi.
assert (MF.f = cF).
tauto.
rewrite <- H6 in |- *.
unfold expf in IHi.
assert (i < p)%nat.
omega.
tauto.
set (zi := Iter (cF m) i x_1) in |- *.
simpl in z.
fold zi in z.
unfold z in |- *.
assert (cF (B m zero x) zi = cF m zi).
rewrite cF_B in |- *.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec (A m zero x) zi).
intros.
assert (cA m zero x = A m zero x).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
rewrite a in H6.
fold x0 in H6.
clear a0.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
unfold x_1 in zi.
assert (zi = Iter (cF m) i (cF m x0)).
unfold zi in |- *.
unfold cF in |- *.
rewrite <- H7 in |- *.
tauto.
assert (zi = Iter (cF m) (S i) x0).
assert (S i = (i + 1)%nat).
omega.
rewrite H9 in |- *.
rewrite MF.Iter_comp in |- *.
simpl in |- *.
tauto.
rewrite <- H6 in H9.
assert (Iter (cF m) 0 x0 = x0).
simpl in |- *.
tauto.
assert (0%nat = S i).
generalize (MF.exd_diff_orb m x0).
intro.
assert (exd m x0).
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
assert (MF.diff_orb m x0).
tauto.
clear H11.
unfold MF.diff_orb in H13.
unfold MF.diff_int in H13.
assert (MF.f = cF).
tauto.
assert (Iter (MF.f m) 0 x0 <> Iter (MF.f m) (S i) x0).
apply H13.
split.
omega.
split.
omega.
assert (p = MF.Iter_upb m x0).
unfold p in |- *.
symmetry in |- *.
assert (x_1 = Iter (MF.f m) 1 x0).
simpl in |- *.
rewrite H11 in |- *.
unfold cF in |- *.
rewrite <- H7 in |- *.
fold x_1 in |- *.
tauto.
rewrite H14 in |- *.
apply MF.period_uniform.
tauto.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
rewrite H14 in H2.
unfold MF.Iter_upb in H2.
unfold MF.Iter_rem in H2.
unfold MF.Iter_upb_aux in |- *.
omega.
simpl in H14.
rewrite H11 in H14.
tauto.
inversion H11.
intros.
elim (eq_dart_dec (bottom m zero x) zi).
intro.
fold xb0 in a0.
rewrite a0 in H1.
elim H1.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with x_1.
unfold x_1 in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H6 in |- *.
fold (cF m x0) in |- *.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H7 in |- *.
tauto.
unfold zi in |- *.
unfold MF.expo in |- *.
split.
tauto.
assert (cF = MF.f).
tauto.
rewrite H6 in |- *.
split with i.
tauto.
intro.
rewrite cA_1_B_ter in |- *.
unfold cF in |- *.
tauto.
tauto.
intro.
inversion H6.
tauto.
tauto.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_B m zero x zi).
assert (exd m zi).
unfold zi in |- *.
generalize (MF.exd_Iter_f m i x_1).
tauto.
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H7 in |- *.
Admitted.

Lemma expf_B0_CS_1_a_prel2:forall (m:fmap)(x z:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in expf m x0 xb0 -> betweenf m x_1 z xb0 -> expf (B m zero x) x_1 z.
Proof.
intros.
generalize H2.
clear H2.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim H2.
clear H2.
intros i Hi.
elim Hi.
clear Hi.
intros j Hj.
unfold x_1 in |- *.
decompose [and] Hj.
clear Hj.
rewrite <- H2.
unfold x_1 in |- *.
apply (expf_B0_CS_1_a_prel1 m x i j).
tauto.
tauto.
fold xb0 in |- *.
fold x_1 in |- *.
symmetry in |- *.
tauto.
fold x_1 in |- *.
omega.
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
