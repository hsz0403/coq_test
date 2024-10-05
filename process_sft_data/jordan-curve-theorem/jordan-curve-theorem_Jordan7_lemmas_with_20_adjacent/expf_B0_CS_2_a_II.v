Require Export Jordan6.

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

Lemma between_expf_B0_2:forall (m:fmap)(x:dart)(i:nat), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in let p:= MF.Iter_upb m xh0_1 in let z:= Iter (cF m) i xh0_1 in ~expf m x0 xb0 -> (i < p)%nat -> expf (B m zero x) xh0_1 z.
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
rename H5 into H4'.
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
generalize (exd_B m zero x xh0_1).
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with (Iter (cF m) i xh0_1).
simpl in IHi.
assert (MF.f = cF).
tauto.
rewrite <- H6 in |- *.
unfold expf in IHi.
assert (i < p)%nat.
omega.
tauto.
set (zi := Iter (cF m) i xh0_1) in |- *.
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
unfold xh0_1 in zi.
fold xh0 in |- *.
assert (xh0 = cA_1 m zero xb0).
unfold xb0 in |- *.
rewrite cA_1_bottom in |- *.
fold xh0 in |- *; tauto.
tauto.
tauto.
assert (xh0_1 = cF m xb0).
unfold xh0_1 in |- *.
unfold cF in |- *.
rewrite <- H8 in |- *.
tauto.
elim H1.
apply expf_trans with xh0_1.
rewrite H6 in |- *.
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold xh0_1 in |- *.
assert (MF.f = cF).
tauto.
rewrite H10 in |- *.
fold zi in |- *.
tauto.
apply expf_symm.
rewrite H9 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold xb0 in |- *.
apply exd_bottom.
tauto.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
intros.
elim (eq_dart_dec (bottom m zero x) zi).
intros.
fold xb0 in a0.
assert (xh0 = cA_1 m zero xb0).
unfold xb0 in |- *.
rewrite cA_1_bottom in |- *.
fold xh0 in |- *; tauto.
tauto.
tauto.
assert (xh0_1 = cF m xb0).
unfold xh0_1 in |- *.
unfold cF in |- *.
rewrite <- H6 in |- *.
tauto.
rewrite a0 in H7.
assert (xh0_1 = Iter (cF m) 0 xh0_1).
simpl in |- *.
tauto.
assert (xh0_1 = Iter (cF m) (S i) xh0_1).
simpl in |- *.
fold zi in |- *.
tauto.
assert (0%nat = S i).
apply (MF.unicity_mod_p m xh0_1 0 (S i)).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
simpl in |- *.
tauto.
inversion H10.
intro.
rewrite cA_1_B_ter in |- *.
fold (cF m zi) in |- *.
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
generalize (MF.exd_Iter_f m i xh0_1).
assert (MF.f = cF).
tauto.
rewrite H7 in |- *.
fold zi in |- *.
tauto.
split with 1%nat.
simpl in |- *.
rewrite <- H6 in |- *.
Admitted.

Lemma expf_xb0_xh0_1:forall (m:fmap)(x:dart), inv_hmap m -> exd m x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in expf m xb0 xh0_1.
Proof.
intros.
assert (xh0 = cA_1 m zero xb0).
unfold xb0 in |- *.
unfold xh0 in |- *.
rewrite cA_1_bottom in |- *.
tauto.
tauto.
tauto.
unfold xh0_1 in |- *.
rewrite H1 in |- *.
assert (exd m xb0).
unfold xb0 in |- *.
apply exd_bottom.
tauto.
tauto.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
assert (MF.f = cF).
tauto.
fold (cF m xb0) in |- *.
rewrite H3 in |- *.
split with 1%nat.
simpl in |- *.
Admitted.

Lemma expf_x0_x_1:forall (m:fmap)(x:dart), inv_hmap m -> exd m x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in expf m x0 x_1.
Proof.
intros.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
unfold x_1 in |- *.
rewrite H1 in |- *.
fold (cF m x0) in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
assert (MF.f = cF).
tauto.
rewrite H2 in |- *.
split with 1%nat.
simpl in |- *.
Admitted.

Lemma expf_transfert:forall (m:fmap)(x z t:dart), inv_hmap m -> exd m x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> (expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t) -> ((expf m x_1 z \/ expf m xh0_1 z) /\ (expf m x_1 t \/ expf m xh0_1 t) \/ expf m z t /\ ~expf m x_1 z /\ ~expf m xh0_1 z).
Proof.
intros.
assert (expf m xb0 xh0_1).
unfold xb0 in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply expf_xb0_xh0_1.
tauto.
tauto.
assert (expf m x0 x_1).
unfold x0 in |- *.
unfold x_1 in |- *.
apply expf_x0_x_1.
tauto.
tauto.
elim (expf_dec m x_1 z).
intro.
elim (expf_dec m x_1 t).
tauto.
elim (expf_dec m xh0_1 t).
tauto.
intros.
assert (~ expf m xb0 t).
intro.
apply b.
apply expf_trans with xb0.
apply expf_symm.
tauto.
tauto.
assert (~ expf m x0 t).
intro.
apply b0.
apply expf_trans with x0.
apply expf_symm.
tauto.
tauto.
assert (expf m z t).
tauto.
absurd (expf m x_1 t).
tauto.
apply expf_trans with z.
tauto.
tauto.
elim (expf_dec m xh0_1 z).
elim (expf_dec m x_1 t).
tauto.
elim (expf_dec m xh0_1 t).
tauto.
intros.
assert (~ expf m x0 z).
intro.
absurd (expf m x_1 z).
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
tauto.
assert (~ expf m xb0 t).
intro.
absurd (expf m xh0_1 t).
tauto.
apply expf_trans with xb0.
apply expf_symm.
tauto.
tauto.
assert (~ expf m x0 t).
intro.
absurd (expf m x_1 t).
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
tauto.
assert (expf m z t).
tauto.
absurd (expf m xh0_1 t).
tauto.
apply expf_trans with z.
tauto.
tauto.
intros.
assert (~ expf m xb0 z).
intro.
absurd (expf m xh0_1 z).
tauto.
apply expf_trans with xb0.
apply expf_symm.
tauto.
tauto.
assert (~ expf m x0 z).
intro.
absurd (expf m x_1 z).
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
tauto.
assert (expf m z t).
tauto.
Admitted.

Lemma expf_B0_x0_xh0_1:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf (B m zero x) x0 xh0_1.
Proof.
intros.
unfold expf in |- *.
split.
apply inv_hmap_B.
tauto.
unfold MF.expo in |- *.
split.
assert (exd m x0).
unfold x0 in |- *.
generalize (exd_cA m zero x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
generalize (exd_B m zero x x0).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H2 in |- *.
rewrite cF_B in |- *.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec (A m zero x) x0).
intro.
rewrite cA_1_B_ter in |- *.
intro.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
tauto.
tauto.
intro.
inversion H3.
unfold x0 in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma expf_B0_xb0_x_1:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf (B m zero x) xb0 x_1.
Proof.
intros.
unfold expf in |- *.
split.
apply inv_hmap_B.
tauto.
unfold MF.expo in |- *.
split.
assert (exd m xb0).
unfold xb0 in |- *.
apply exd_bottom.
tauto.
apply succ_exd with zero.
tauto.
tauto.
generalize (exd_B m zero x xb0).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H2 in |- *.
rewrite cF_B in |- *.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec (A m zero x) xb0).
intro.
rewrite cA_1_B_ter in |- *.
symmetry in a.
unfold xb0 in a.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
tauto.
intro.
inversion H3.
elim (eq_dart_dec (bottom m zero x) xb0).
intros.
rewrite cA_1_B_ter in |- *.
unfold x_1 in |- *.
tauto.
tauto.
intro.
inversion H3.
unfold xb0 in |- *.
tauto.
tauto.
tauto.
Admitted.

Lemma expf_B0_CS_2_a_I:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf m x_1 z -> expf m x_1 t -> expf (B m zero x) z t.
Proof.
intros.
assert (MF.expo1 m x_1 z).
generalize (MF.expo_expo1 m x_1 z H).
unfold expf in H2.
tauto.
assert (MF.expo1 m x_1 t).
generalize (MF.expo_expo1 m x_1 t H).
unfold expf in H3.
tauto.
unfold MF.expo1 in H4.
unfold MF.expo1 in H5.
elim H4.
intros.
clear H4.
elim H5.
intros.
clear H5.
clear H4.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H7.
fold p in H8.
elim H7.
clear H7.
intros i Hi.
elim H8.
intros j Hj.
clear H8.
elim Hi.
clear Hi.
intros Ci Hi.
elim Hj; clear Hj.
intros Cj Hj.
assert (expf (B m zero x) x_1 z).
rewrite <- Hi in |- *.
unfold x_1 in |- *.
apply between_expf_B0_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold p in |- *.
tauto.
assert (expf (B m zero x) x_1 t).
rewrite <- Hj in |- *.
unfold x_1 in |- *.
apply between_expf_B0_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold p in |- *.
tauto.
apply expf_trans with x_1.
apply expf_symm.
tauto.
Admitted.

Lemma xb0_ind:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in let p := MF.Iter_upb m xh0_1 in xb0 = Iter (cF m) (p-1)%nat xh0_1.
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
assert (exd m xb0).
unfold xb0 in |- *.
apply exd_bottom.
tauto.
tauto.
assert (exd m xh0_1).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
tauto.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H5 in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite <- H6 in |- *.
rewrite H5 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold xh0_1 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
unfold xh0 in |- *.
unfold xb0 in |- *.
rewrite cA_top in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
generalize (MF.upb_pos m xh0_1 H4).
intro.
fold p in H5.
Admitted.

Lemma x0_ind:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in let p := MF.Iter_upb m x_1 in x0 = Iter (cF m) (p-1)%nat x_1.
Proof.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m x0).
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (cF = MF.f).
tauto.
assert (cF_1 = MF.f_1).
tauto.
rewrite H4 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold x_1 in |- *.
rewrite <- H5 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
generalize (MF.upb_pos m x_1 H3).
fold p in |- *.
intro.
Admitted.

Lemma expf_B0_CS_2_a_III:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf m xh0_1 z -> expf m x_1 t -> expf (B m zero x) z t.
Proof.
intros.
assert (MF.expo1 m xh0_1 z).
generalize (MF.expo_expo1 m xh0_1 z H).
unfold expf in H2.
tauto.
assert (MF.expo1 m x_1 t).
generalize (MF.expo_expo1 m x_1 t H).
unfold expf in H3.
tauto.
unfold MF.expo1 in H4.
unfold MF.expo1 in H5.
elim H4.
intros.
clear H4.
elim H5.
intros.
clear H5.
clear H4.
set (p := MF.Iter_upb m xh0_1) in |- *.
fold p in H7.
set (q := MF.Iter_upb m x_1) in |- *.
fold q in H8.
elim H7.
clear H7.
intros i Hi.
elim H8.
intros j Hj.
clear H8.
elim Hi.
clear Hi.
intros Ci Hi.
elim Hj; clear Hj.
intros Cj Hj.
assert (expf (B m zero x) xh0_1 z).
rewrite <- Hi in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply between_expf_B0_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold p in |- *.
tauto.
assert (expf (B m zero x) x_1 t).
rewrite <- Hj in |- *.
unfold x_1 in |- *.
apply between_expf_B0_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold q in |- *.
tauto.
assert (x0 = Iter (cF m) (q - 1) x_1).
unfold x_1 in |- *.
unfold q in |- *.
unfold x_1 in |- *.
rewrite <- x0_ind in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
assert (xb0 = Iter (cF m) (p - 1) xh0_1).
unfold p in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
rewrite <- xb0_ind in |- *.
fold xb0 in |- *.
tauto.
tauto.
tauto.
assert (expf (B m zero x) x_1 x0).
rewrite H7 in |- *.
unfold x_1 in |- *.
apply between_expf_B0_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold q in |- *.
omega.
assert (expf (B m zero x) xh0_1 xb0).
rewrite H8 in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply between_expf_B0_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold p in |- *.
omega.
assert (expf (B m zero x) xb0 x_1).
unfold xb0 in |- *.
unfold x_1 in |- *.
apply expf_B0_xb0_x_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
assert (expf (B m zero x) x0 xh0_1).
unfold x0 in |- *; unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply expf_B0_x0_xh0_1.
tauto.
tauto.
tauto.
fold xb0 in |- *.
fold x0 in |- *.
apply expf_trans with xh0_1.
apply expf_symm.
tauto.
apply expf_trans with xb0.
tauto.
apply expf_trans with x_1.
tauto.
Admitted.

Lemma expf_B0_CS_2_a_IV:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf m x_1 z -> expf m xh0_1 t -> expf (B m zero x) z t.
Proof.
intros.
assert (MF.expo1 m xh0_1 t).
generalize (MF.expo_expo1 m xh0_1 t H).
unfold expf in H3.
tauto.
assert (MF.expo1 m x_1 z).
generalize (MF.expo_expo1 m x_1 z H).
unfold expf in H2.
tauto.
unfold MF.expo1 in H4.
unfold MF.expo1 in H5.
elim H4.
intros.
clear H4.
elim H5.
intros.
clear H5.
clear H4.
set (p := MF.Iter_upb m xh0_1) in |- *.
fold p in H7.
set (q := MF.Iter_upb m x_1) in |- *.
fold q in H8.
elim H7.
clear H7.
intros i Hi.
elim H8.
intros j Hj.
clear H8.
elim Hi.
clear Hi.
intros Ci Hi.
elim Hj; clear Hj.
intros Cj Hj.
assert (expf (B m zero x) xh0_1 t).
rewrite <- Hi in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply between_expf_B0_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold p in |- *.
tauto.
assert (expf (B m zero x) x_1 z).
rewrite <- Hj in |- *.
unfold x_1 in |- *.
apply between_expf_B0_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold q in |- *.
tauto.
assert (x0 = Iter (cF m) (q - 1) x_1).
unfold x_1 in |- *.
unfold q in |- *.
unfold x_1 in |- *.
rewrite <- x0_ind in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
assert (xb0 = Iter (cF m) (p - 1) xh0_1).
unfold p in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
rewrite <- xb0_ind in |- *.
fold xb0 in |- *.
tauto.
tauto.
tauto.
assert (expf (B m zero x) x_1 x0).
rewrite H7 in |- *.
unfold x_1 in |- *.
apply between_expf_B0_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold q in |- *.
omega.
assert (expf (B m zero x) xh0_1 xb0).
rewrite H8 in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply between_expf_B0_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold p in |- *.
omega.
assert (expf (B m zero x) xb0 x_1).
unfold xb0 in |- *.
unfold x_1 in |- *.
apply expf_B0_xb0_x_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
assert (expf (B m zero x) x0 xh0_1).
unfold x0 in |- *; unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply expf_B0_x0_xh0_1.
tauto.
tauto.
fold xb0 in |- *.
fold x0 in |- *.
tauto.
apply expf_trans with xh0_1.
apply expf_trans with x0.
apply expf_trans with x_1.
apply expf_symm.
tauto.
tauto.
tauto.
Admitted.

Lemma expf_B0_CS_2_a:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> (expf m x_1 z \/ expf m xh0_1 z) /\ (expf m x_1 t \/ expf m xh0_1 t) -> expf (B m zero x) z t.
Proof.
intros.
decompose [and] H2.
clear H2.
elim H3.
clear H3.
elim H4.
clear H4.
intros.
apply expf_B0_CS_2_a_I.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
clear H4.
intros.
apply expf_B0_CS_2_a_IV.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
clear H3.
elim H4.
clear H4.
intros.
apply expf_B0_CS_2_a_III.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold xh0 in |- *; fold xh0_1 in |- *.
tauto.
fold x_1 in |- *.
tauto.
clear H4.
intros.
apply expf_B0_CS_2_a_II.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
Admitted.

Lemma expf_B0_CS_2_b_ind:forall (m:fmap)(x z:dart)(i:nat), inv_hmap m -> succ m zero x -> exd m z -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> let t:=Iter (cF m) i z in ~expf m x_1 z -> ~expf m xh0_1 z -> expf (B m zero x) z t.
Proof.
intros.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
assert (exd (B m zero x) z).
generalize (exd_B m zero x z).
tauto.
assert (MF.f = cF).
tauto.
induction i.
simpl in t.
unfold t in |- *.
apply expf_refl.
tauto.
tauto.
simpl in t.
set (zi := Iter (cF m) i z) in |- *.
simpl in IHi.
fold zi in IHi.
unfold t in |- *.
fold zi in |- *.
apply expf_trans with zi.
tauto.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
assert (exd m zi).
unfold zi in |- *.
generalize (MF.exd_Iter_f m i z).
tauto.
assert (exd (B m zero x) zi).
generalize (exd_B m zero x zi).
tauto.
split.
tauto.
rewrite H7 in |- *.
split with 1%nat.
simpl in |- *.
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
clear a0.
fold x0 in H10.
rewrite a in H10.
assert (expf m z zi).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
rewrite H7 in |- *.
tauto.
absurd (expf m x_1 z).
tauto.
apply expf_trans with x0.
apply expf_symm.
unfold x0 in |- *.
unfold x_1 in |- *.
apply expf_x0_x_1.
tauto.
apply succ_exd with zero.
tauto.
tauto.
rewrite H10 in |- *.
apply expf_symm.
tauto.
elim (eq_dart_dec (bottom m zero x) zi).
intros.
rewrite cA_1_B_ter in |- *.
fold xb0 in a.
assert (expf m z zi).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
rewrite H7 in |- *.
tauto.
absurd (expf m xh0_1 z).
tauto.
apply expf_trans with xb0.
apply expf_symm.
unfold xb0 in |- *; unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply expf_xb0_xh0_1.
tauto.
apply succ_exd with zero.
tauto.
tauto.
apply expf_trans with zi.
rewrite a in |- *.
apply expf_refl.
tauto.
tauto.
apply expf_symm.
tauto.
tauto.
intro.
inversion H10.
rewrite cA_1_B_ter in |- *.
unfold cF in |- *.
tauto.
tauto.
intro.
inversion H10.
tauto.
tauto.
Admitted.

Lemma expf_B0_CS_2_b:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf m z t -> ~expf m x_1 z -> ~expf m xh0_1 z -> expf (B m zero x) z t.
Proof.
intros.
unfold expf in H2.
decompose [and] H2.
clear H2.
unfold MF.expo in H6.
elim H6.
intros.
clear H6.
elim H7.
clear H7.
intros i Hi.
rewrite <- Hi in |- *.
apply expf_B0_CS_2_b_ind.
tauto.
tauto.
tauto.
fold xb0 in |- *.
fold x0 in |- *; tauto.
fold x_1 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
Admitted.

Lemma expf_B0_CS_2_aux:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> ((expf m x_1 z \/ expf m xh0_1 z) /\ (expf m x_1 t \/ expf m xh0_1 t) \/ expf m z t /\ ~expf m x_1 z /\ ~expf m xh0_1 z) -> expf (B m zero x) z t.
Proof.
intros.
elim H2.
intro.
apply expf_B0_CS_2_a.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
clear H2.
intro.
apply expf_B0_CS_2_b.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
tauto.
fold x_1 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
Admitted.

Lemma expf_B0_CS_2:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in ~expf m x0 xb0 -> (expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t) -> expf (B m zero x) z t.
intros.
intros.
set (x_1 := cA_1 m one x) in |- *.
set (xh0 := top m zero x) in |- *.
set (xh0_1 := cA_1 m one xh0) in |- *.
assert ((expf m x_1 z \/ expf m xh0_1 z) /\ (expf m x_1 t \/ expf m xh0_1 t) \/ expf m z t /\ ~ expf m x_1 z /\ ~ expf m xh0_1 z).
unfold x_1 in |- *; unfold xh0_1 in |- *; unfold xh0 in |- *.
apply expf_transfert.
tauto.
apply succ_exd with zero.
tauto.
tauto.
fold x0 in |- *; fold xb0 in |- *.
tauto.
fold xb0 in |- *.
fold x0 in |- *.
tauto.
apply expf_B0_CS_2_aux.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xh0 in |- *.
fold xh0_1 in |- *.
Admitted.

Theorem expf_B0_CS:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in (if expf_dec m x0 xb0 then betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0 \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t) -> expf (B m zero x) z t.
Proof.
intros.
generalize H1.
clear H1.
elim (expf_dec m x0 xb0).
intros.
apply expf_B0_CS_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xh0 in |- *.
fold xh0_1 in |- *.
tauto.
intro.
intro.
apply expf_B0_CS_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
Admitted.

Lemma expf_B0_CN_i:forall (m:fmap)(x z:dart)(i:nat), inv_hmap m -> succ m zero x -> exd m z -> let t:= Iter (MF.f (B m zero x)) i z in let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in (if expf_dec m x0 xb0 then betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0 \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t).
Proof.
induction i.
simpl in |- *.
set (x0 := cA m zero x) in |- *.
set (xb0 := bottom m zero x) in |- *.
set (x_1 := cA_1 m one x) in |- *.
set (xh0 := top m zero x) in |- *.
set (xh0_1 := cA_1 m one xh0) in |- *.
elim (expf_dec m x0 xb0).
intros.
rename H1 into E1.
elim (expf_dec m x_1 z).
intro.
assert (expf m x_1 xb0).
apply expf_trans with x0.
apply expf_symm.
unfold x_1 in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
rewrite H1 in |- *.
fold (cF m x0) in |- *.
assert (cF = MF.f).
tauto.
rewrite H2 in |- *.
unfold expf in |- *.
split.
tauto.
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
tauto.
assert (MF.expo1 m x_1 z).
generalize (MF.expo_expo1 m x_1 z).
unfold expf in a0.
tauto.
assert (MF.expo1 m x_1 xb0).
generalize (MF.expo_expo1 m x_1 xb0).
unfold expf in H1.
tauto.
generalize (MF.expo_between_3 m x_1 xb0 z H H3 H2).
intros.
assert (xh0_1 = MF.f m xb0).
unfold xh0_1 in |- *.
unfold xh0 in |- *.
unfold xb0 in |- *.
assert (MF.f = cF).
tauto.
rewrite H5 in |- *.
unfold cF in |- *.
rewrite cA_1_bottom in |- *.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
assert (x0 = MF.f_1 m x_1).
assert (MF.f_1 = cF_1).
tauto.
rewrite H6 in |- *.
unfold cF_1 in |- *.
assert (x = cA m one x_1).
unfold x_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
rewrite <- H7 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H5 in H4.
rewrite <- H6 in H4.
unfold betweenf in |- *.
tauto.
intro.
right.
right.
split.
tauto.
apply expf_refl.
tauto.
tauto.
intros.
right.
right.
apply expf_refl.
tauto.
tauto.
intros.
generalize (IHi H H0 H1).
clear IHi.
intro.
simpl in H2.
fold x0 in H2.
fold xb0 in H2.
fold x_1 in H2.
fold xh0 in H2.
fold xh0_1 in H2.
set (ti := Iter (MF.f (B m zero x)) i z) in |- *.
fold ti in H2.
generalize H2.
clear H2.
simpl in t.
fold ti in t.
assert (MF.f = cF).
tauto.
assert (MF.f (B m zero x) ti = cF (B m zero x) ti).
rewrite H2 in |- *.
tauto.
fold t in H3.
rewrite cF_B in H3.
generalize H3.
clear H3.
elim (eq_dim_dec zero zero).
intro.
clear a.
rewrite cA_1_B_ter in |- *.
intro.
elim (expf_dec m x0 xb0).
intros.
elim H4.
clear H4.
intro.
elim (eq_dart_dec ti xb0).
intro.
left.
split.
tauto.
generalize H3.
elim (eq_dart_dec (A m zero x) ti).
intros.
rewrite a0 in a1.
unfold xb0 in a1.
absurd (bottom m zero x <> A m zero x).
symmetry in a1.
tauto.
apply succ_bottom.
tauto.
tauto.
intro.
elim (eq_dart_dec (bottom m zero x) ti).
intro.
intro.
fold x_1 in H5.
rewrite H5 in |- *.
clear H3.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
generalize (MF.between_expo_refl_1 m x_1 xb0 H H3).
intros.
unfold betweenf in H4.
generalize (MF.between_expo1 m x_1 z xb0 H H3).
tauto.
symmetry in a0.
unfold xb0 in a0.
tauto.
intro.
left.
split.
tauto.
decompose [and] H4.
clear H4.
generalize H6; clear H6.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
generalize (H6 H4 H7).
clear H6.
intro.
elim H6.
clear H6.
intros iti Hiti.
elim Hiti.
clear Hiti.
intros j Hj.
decompose [and] Hj.
clear Hj.
assert (iti <> j).
intro.
rewrite H10 in H6.
rewrite H6 in H9.
tauto.
split with (S iti).
split with j.
split.
simpl in |- *.
generalize H3.
elim (eq_dart_dec (A m zero x) ti).
intro.
intro.
clear H3.
assert (cA m zero x = A m zero x).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
fold x0 in H3.
rewrite a0 in H3.
rewrite <- H3 in H6.
assert (x_1 = MF.f m x0).
unfold x_1 in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
rewrite H2 in |- *.
unfold cF in |- *.
rewrite H13 in |- *.
tauto.
assert (Iter (MF.f m) (S iti) x_1 = x_1).
simpl in |- *.
rewrite H6 in |- *.
symmetry in |- *.
tauto.
assert (S iti = 0%nat).
apply (MF.unicity_mod_p m x_1 (S iti) 0 H H7).
omega.
apply MF.upb_pos.
tauto.
simpl in |- *.
simpl in H14.
tauto.
inversion H15.
intro.
elim (eq_dart_dec (bottom m zero x) ti).
fold xb0 in |- *.
intro.
symmetry in a0.
tauto.
fold (cF m ti) in |- *.
rewrite <- H2 in |- *.
intros.
rewrite H6 in |- *.
symmetry in |- *.
tauto.
split.
tauto.
omega.
clear H4.
intro.
elim H4.
clear H4.
intro.
right.
left.
assert (cA m zero x = A m zero x).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
fold x0 in H5.
assert (x_1 = MF.f m x0).
unfold x_1 in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
rewrite H6 in |- *.
rewrite H2 in |- *.
unfold cF in |- *.
tauto.
split.
tauto.
generalize H3; clear H3.
elim (eq_dart_dec (A m zero x) ti).
intros.
fold xh0 in |- *.
fold xh0 in H3.
fold xh0_1 in H3.
rewrite H3 in |- *.
decompose [and] H4.
clear H4.
generalize H8; clear H8.
unfold betweenf in |- *.
intros.
assert (exd m xh0_1).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
assert (exd m xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x H).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
tauto.
generalize (MF.between_expo1 m xh0_1 z x0 H H4 H7).
intro.
generalize (MF.between_expo_refl_1 m xh0_1 x0 H H4).
tauto.
elim (eq_dart_dec (bottom m zero x) ti).
fold xb0 in |- *.
intros.
fold x_1 in H3.
rewrite <- H5 in b.
decompose [and] H4.
clear H4.
rewrite <- a0 in H8.
rewrite <- a0 in b.
assert (cF m xb0 = xh0_1).
unfold xh0_1 in |- *.
unfold xh0 in |- *.
rewrite <- top_bottom_bis in |- *.
fold xb0 in |- *.
rewrite <- cA_1_top in |- *.
fold (cF m xb0) in |- *.
tauto.
tauto.
unfold xb0 in |- *.
generalize (exd_bottom m zero x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
unfold xb0 in |- *.
apply not_pred_bottom.
tauto.
tauto.
apply succ_exd with zero.
tauto.
tauto.
unfold betweenf in H8.
unfold MF.between in H8.
assert (exd m xh0_1).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
assert (exd m xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x H).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
tauto.
generalize (H8 H H9).
clear H8.
intro.
elim H8.
intros i1 Hi.
clear H8.
elim Hi; clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
assert (i1 <> j).
intro.
rewrite H12 in H8.
rewrite H11 in H8.
tauto.
assert (Iter (MF.f m) (S i1) xh0_1 = xh0_1).
simpl in |- *.
rewrite H8 in |- *.
rewrite H2 in |- *.
tauto.
assert (S i1 = 0%nat).
apply (MF.unicity_mod_p m xh0_1 (S i1) 0 H H9).
omega.
apply MF.upb_pos.
tauto.
simpl in |- *.
simpl in H14.
tauto.
inversion H15.
intros.
fold (cF m ti) in H3.
rewrite <- H5 in b0.
fold xb0 in b.
decompose [and] H4.
clear H4.
generalize H8.
clear H8.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
generalize (H8 H4 H9).
clear H8.
intro.
elim H8; clear H8.
intros iti Hiti.
elim Hiti.
clear Hiti.
intros j Hj.
decompose [and] Hj.
clear Hj.
assert (iti <> j).
intro.
rewrite H12 in H8.
rewrite H11 in H8.
tauto.
split with (S iti).
split with j.
split.
simpl in |- *.
rewrite H8 in |- *.
rewrite H2 in |- *.
symmetry in |- *.
tauto.
split.
tauto.
split.
omega.
omega.
clear H4.
intro.
right.
right.
split.
tauto.
decompose [and] H4.
clear H4.
generalize H3.
clear H3.
elim (eq_dart_dec (A m zero x) ti).
intros.
assert (x0 = A m zero x).
unfold x0 in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
generalize H3.
clear H3.
rewrite <- top_bottom_bis in |- *.
fold xb0 in |- *.
assert (top m zero xb0 = cA_1 m zero xb0).
rewrite cA_1_eq in |- *.
elim (pred_dec m zero xb0).
unfold xb0 in |- *.
intro.
absurd (pred m zero (bottom m zero x)).
apply not_pred_bottom.
tauto.
tauto.
tauto.
tauto.
rewrite H3 in |- *.
fold (cF m xb0) in |- *.
intro.
assert (expf m xb0 t).
unfold t in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold xb0 in |- *.
generalize (exd_bottom m zero x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
fold t in |- *.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *; symmetry in |- *; tauto.
apply expf_trans with ti.
tauto.
rewrite <- a0 in |- *.
rewrite <- H4 in |- *.
apply expf_trans with xb0.
tauto.
tauto.
tauto.
apply succ_exd with zero.
tauto; tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) ti).
fold xb0 in |- *; intros.
rewrite <- a0 in H6.
assert (expf m x0 x_1).
unfold x_1 in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
apply succ_exd with zero; tauto; tauto.
rewrite H4 in |- *.
fold (cF m x0) in |- *.
assert (exd m x).
apply succ_exd with zero; tauto; tauto.
assert (exd m x0).
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
fold x_1 in H3.
apply expf_trans with xb0.
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
rewrite H3 in |- *.
tauto.
fold (cF m ti) in |- *.
intros.
apply expf_trans with ti.
tauto.
rewrite H3 in |- *.
generalize H6.
unfold expf in |- *.
intro.
split.
tauto.
unfold MF.expo in |- *.
split.
generalize (MF.expo_exd m z ti).
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (x0 = A m zero x).
unfold x0 in |- *.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
assert (exd m xb0).
unfold xb0 in |- *.
generalize (exd_bottom m zero x).
tauto.
assert (exd m x0).
rewrite H6 in |- *.
apply succ_exd_A.
tauto.
tauto.
elim H4.
clear H4.
intro.
decompose [and] H4.
clear H4.
generalize H3.
clear H3.
elim (eq_dart_dec (A m zero x) ti).
rewrite <- top_bottom_bis in |- *.
fold xb0 in |- *.
assert (top m zero xb0 = cA_1 m zero xb0).
rewrite cA_1_eq in |- *.
elim (pred_dec m zero xb0).
unfold xb0 in |- *.
intro.
absurd (pred m zero (bottom m zero x)).
apply not_pred_bottom.
tauto.
tauto.
tauto.
tauto.
rewrite H3 in |- *.
rewrite <- H6 in |- *.
intros.
fold (cF m xb0) in H4.
right.
right.
apply expf_trans with xb0.
apply expf_symm.
tauto.
rewrite H4 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
tauto.
tauto.
intro.
rewrite <- H6 in b0.
elim (eq_dart_dec (bottom m zero x) ti).
fold xb0 in |- *.
intro.
rewrite <- a in H10.
tauto.
fold (cF m ti) in |- *.
intros.
left.
split.
tauto.
apply expf_trans with ti.
tauto.
rewrite H3 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold expf in H10.
generalize (MF.expo_exd m x0 ti).
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
clear H4.
intros.
elim H4.
clear H4.
intro.
generalize H3.
clear H3.
elim (eq_dart_dec (A m zero x) ti).
rewrite <- H6 in |- *.
rewrite <- top_bottom_bis in |- *.
fold xb0 in |- *.
assert (top m zero xb0 = cA_1 m zero xb0).
rewrite cA_1_eq in |- *.
elim (pred_dec m zero xb0).
unfold xb0 in |- *.
intro.
absurd (pred m zero (bottom m zero x)).
apply not_pred_bottom.
tauto.
tauto.
tauto.
tauto.
rewrite H3 in |- *.
fold (cF m xb0) in |- *.
right.
left.
split.
rewrite H9 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
tauto.
tauto.
tauto.
elim (eq_dart_dec (bottom m zero x) ti).
fold xb0 in |- *.
rewrite <- H6 in |- *.
intros.
fold x_1 in H3.
right.
right.
apply expf_trans with x0.
apply expf_symm.
tauto.
rewrite H3 in |- *.
unfold x_1 in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H9 in |- *.
fold (cF m x0) in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
fold (cF m ti) in |- *.
intros.
rewrite <- H6 in b1.
fold xb0 in b0.
right.
left.
split.
apply expf_trans with ti.
tauto.
rewrite H3 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
decompose [and] H4.
clear H4.
unfold expf in H9.
generalize (MF.expo_exd m xb0 ti).
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
tauto.
clear H4.
intro.
generalize H3; clear H3.
rewrite <- H6 in |- *.
elim (eq_dart_dec x0 ti).
rewrite <- top_bottom_bis in |- *.
fold xb0 in |- *.
assert (top m zero xb0 = cA_1 m zero xb0).
rewrite cA_1_eq in |- *.
elim (pred_dec m zero xb0).
unfold xb0 in |- *.
intro.
absurd (pred m zero (bottom m zero x)).
apply not_pred_bottom.
tauto.
tauto.
tauto.
tauto.
rewrite H3 in |- *.
fold (cF m xb0) in |- *.
intros.
right.
left.
split.
rewrite H9 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
rewrite a in |- *.
apply expf_symm.
tauto.
tauto.
tauto.
fold xb0 in |- *.
elim (eq_dart_dec xb0 ti).
fold x_1 in |- *.
intros.
left.
split.
rewrite a in |- *.
apply expf_symm.
tauto.
rewrite H3 in |- *.
unfold x_1 in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H9 in |- *.
fold (cF m x0) in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
fold (cF m ti) in |- *.
intros.
right.
right.
apply expf_trans with ti.
tauto.
rewrite H3 in |- *.
unfold expf in H4.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
generalize (MF.expo_exd m z ti).
tauto.
split with 1%nat.
simpl in |- *.
rewrite H2 in |- *.
tauto.
tauto.
intro.
inversion H3.
tauto.
tauto.
Admitted.

Lemma expf_B0_CN:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> expf (B m zero x) z t -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in (if expf_dec m x0 xb0 then betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0 \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t).
Proof.
intros.
unfold expf in H1.
unfold MF.expo in H1.
decompose [and] H1.
clear H1.
elim H5.
clear H5.
intros i Hi.
assert (exd m z).
generalize (exd_B m zero x z).
tauto.
unfold x0 in |- *.
unfold x_1 in |- *; unfold xh0_1 in |- *; unfold xh0 in |- *.
unfold xb0 in |- *.
rewrite <- Hi in |- *.
apply expf_B0_CN_i.
tauto.
tauto.
Admitted.

Theorem expf_B0_CNS:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> (expf (B m zero x) z t <-> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in (if expf_dec m x0 xb0 then betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0 \/ betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m xb0 z /\ expf m x0 t \/ expf m xb0 t /\ expf m x0 z \/ expf m z t)).
Proof.
simpl in |- *.
split.
apply expf_B0_CN.
tauto.
tauto.
apply expf_B0_CS.
tauto.
Admitted.

Theorem expf_not_expf_B0: forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let x_1:= cA_1 m one x in let x0 := cA m zero x in let xb0 := bottom m zero x in (expf (B m zero x) x_1 x0 <-> ~expf m x0 xb0).
Proof.
intros.
split.
intro.
generalize (expf_B0_CN m x x_1 x0 H H0 H1).
simpl in |- *.
fold x_1 in |- *.
fold xb0 in |- *.
fold x0 in |- *.
set (xh0 := top m zero x) in |- *.
set (xh0_1 := cA_1 m one xh0) in |- *.
elim (expf_dec m x0 xb0).
intros.
elim H2; clear H2.
intro.
elim H2.
clear H2.
intros.
elim (eq_dart_dec x0 xb0).
intro.
unfold x0 in a0.
unfold xb0 in a0.
generalize a0.
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
intros.
symmetry in a2.
absurd (bottom m zero x = A m zero x).
apply succ_bottom.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
unfold betweenf in H3.
unfold MF.between in H3.
elim H3.
intros i Hi.
clear H3.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H7.
assert (x0 = Iter (cF m) (p - 1) x_1).
unfold x_1 in |- *.
unfold p in |- *.
unfold x_1 in |- *.
rewrite <- x0_ind in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
rewrite H6 in H3.
assert (cF = MF.f).
tauto.
rewrite H8 in H3.
assert (i = (p - 1)%nat).
apply (MF.unicity_mod_p m x_1).
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
generalize (exd_cA_1 m one x).
unfold x_1 in |- *.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
tauto.
fold p in Hj.
decompose [and] Hj.
assert (i = j).
omega.
rewrite H13 in H10.
rewrite H10 in H12.
tauto.
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
generalize (exd_cA_1 m one x).
unfold x_1 in |- *.
tauto.
intros.
elim H2.
clear H2.
intros.
elim H2.
clear H2.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
unfold betweenf in H2.
unfold MF.between in H2.
elim H2.
intros i Hi.
clear H2.
elim Hi.
intros j Hj.
clear Hi.
decompose [and] Hj.
set (p := MF.Iter_upb m xh0_1) in |- *.
fold p in H8.
clear Hj.
assert (x_1 = cF m x0).
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
rewrite H7 in H2.
rewrite <- H6 in H2.
assert (MF.f = cF).
tauto.
rewrite <- H9 in H2.
assert (MF.f m (Iter (MF.f m) j xh0_1) = Iter (MF.f m) (S j) xh0_1).
simpl in |- *.
tauto.
rewrite H10 in H2.
elim (eq_nat_dec (S j) p).
intro.
rewrite a0 in H2.
unfold p in H2.
rewrite MF.Iter_upb_period in H2.
assert (x_1 = xh0_1).
rewrite H7 in |- *.
rewrite <- H6 in |- *.
rewrite <- H9 in |- *.
rewrite H10 in |- *.
rewrite a0 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x).
tauto.
unfold x_1 in H11.
assert (x = xh0).
assert (cA m one x_1 = cA m one xh0_1).
fold x_1 in H11.
rewrite H11 in |- *.
tauto.
unfold x_1 in H12.
unfold xh0_1 in H12.
rewrite cA_cA_1 in H12.
rewrite cA_cA_1 in H12.
tauto.
tauto.
unfold xh0 in |- *.
apply exd_top.
tauto.
tauto.
tauto.
tauto.
unfold xh0 in H12.
absurd (succ m zero x).
rewrite H12 in |- *.
apply not_succ_top.
tauto.
tauto.
tauto.
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x).
tauto.
intro.
assert (i = S j).
apply (MF.unicity_mod_p m xh0_1 i (S j) H).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x).
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
tauto.
absurd (i = S j).
omega.
tauto.
tauto.
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
unfold xh0 in |- *.
generalize (exd_top m zero x).
tauto.
clear H2.
intro.
absurd (expf m x_1 x_1).
tauto.
apply expf_refl.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
tauto.
intro.
generalize (expf_B0_CS m x x_1 x0).
simpl in |- *.
fold x_1 in |- *.
fold xb0 in |- *.
set (xh0 := top m zero x) in |- *.
set (xh0_1 := cA_1 m one xh0) in |- *.
fold x0 in |- *.
intros.
generalize (H2 H H0).
clear H2.
elim (expf_dec m x0 xb0).
tauto.
intros.
apply H2.
clear H2.
clear b.
right.
right.
apply expf_symm.
unfold x0 in |- *.
unfold x_1 in |- *.
apply expf_x0_x_1.
tauto.
apply succ_exd with zero.
tauto.
Admitted.

Lemma inv_hmap_L0L0:forall (m:fmap)(x y x' y':dart), let m1:= L (L m zero x y) zero x' y' in let m2:= L (L m zero x' y') zero x y in inv_hmap m1 -> inv_hmap m2.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
intros.
decompose [and] H.
clear H.
generalize H8 H9 H11.
clear H8 H9 H11.
elim (eq_dart_dec x x').
intros.
absurd (y <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec y y').
intros.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec (cA_1 m zero y) x').
intros.
intros.
split.
assert (cA m zero x' <> y').
intro.
rewrite <- a in H.
rewrite cA_cA_1 in H.
tauto.
tauto.
tauto.
tauto.
split.
tauto.
split.
tauto.
elim (eq_dart_dec x' x).
intro.
symmetry in a0.
tauto.
elim (eq_dart_dec y' y).
intro.
symmetry in a0.
tauto.
elim (eq_dart_dec (cA_1 m zero y') x).
intro.
rewrite <- a0 in H11.
rewrite cA_cA_1 in H11.
tauto.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec x' x).
intro.
symmetry in a.
tauto.
elim (eq_dart_dec y' y).
intro.
symmetry in a.
tauto.
elim (eq_dart_dec (cA_1 m zero y') x).
intro.
assert (cA m zero x' <> y).
intro.
rewrite <- H in b.
rewrite cA_1_cA in b.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma inv_hmap_L0L1:forall (m:fmap)(x y x' y':dart), let m1:= L (L m zero x y) one x' y' in let m2:= L (L m one x' y') zero x y in inv_hmap m1 -> inv_hmap m2.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
intros.
decompose [and] H.
clear H.
Admitted.

Lemma betweenf_expf:forall(m:fmap)(z v t:dart), inv_hmap m -> exd m z -> betweenf m z v t -> (expf m z v /\ expf m z t).
Proof.
unfold betweenf in |- *.
unfold expf in |- *.
intros.
generalize (MF.between_expo1 m z v t H H0 H1).
intros.
generalize (MF.expo_expo1 m z v).
generalize (MF.expo_expo1 m z t).
Admitted.

Lemma B0_L0_L0:forall (m:fmap)(x y x' y':dart), let m1 := L (L m zero x y) zero x' y' in inv_hmap m1 -> B m1 zero x = L m zero x' y'.
Proof.
simpl in |- *.
intros.
decompose [and] H.
clear H.
unfold prec_L in H1.
unfold succ in H1.
unfold pred in H1.
simpl in H1.
decompose [and] H1.
clear H1.
generalize H0 H5.
clear H0 H5.
unfold prec_L in H3.
generalize H7.
clear H7.
unfold succ in H3.
unfold pred in H3.
decompose [and] H3.
clear H3.
elim (eq_dart_dec x x').
intros.
absurd (y <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec y y').
intros.
absurd (x <> nil).
tauto.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec x' x).
intro.
rewrite a in |- *.
tauto.
elim (eq_dart_dec x x).
tauto.
Admitted.

Lemma B0_L1_L0:forall (m:fmap)(x y x' y':dart), let m1 := L (L m zero x y) one x' y' in inv_hmap m1 -> B m1 zero x = L m one x' y'.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
elim (eq_dart_dec x x).
tauto.
Admitted.

Lemma B1_L0_L1:forall (m:fmap)(x y x' y':dart), let m1 := L (L m one x y) zero x' y' in inv_hmap m1 -> B m1 one x = L m zero x' y'.
Proof.
simpl in |- *.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
simpl in |- *.
intros m x y x' y'.
elim (eq_dart_dec x x).
tauto.
Admitted.

Lemma expf_B0_CS_2_a_II:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf m xh0_1 z -> expf m xh0_1 t -> expf (B m zero x) z t.
Proof.
intros.
assert (MF.expo1 m xh0_1 z).
generalize (MF.expo_expo1 m xh0_1 z H).
unfold expf in H2.
tauto.
assert (MF.expo1 m xh0_1 t).
generalize (MF.expo_expo1 m xh0_1 t H).
unfold expf in H3.
tauto.
unfold MF.expo1 in H4.
unfold MF.expo1 in H5.
elim H4.
intros.
clear H4.
elim H5.
intros.
clear H5.
clear H4.
set (p := MF.Iter_upb m xh0_1) in |- *.
fold p in H7.
fold p in H8.
elim H7.
clear H7.
intros i Hi.
elim H8.
intros j Hj.
clear H8.
elim Hi.
clear Hi.
intros Ci Hi.
elim Hj; clear Hj.
intros Cj Hj.
assert (expf (B m zero x) xh0_1 z).
rewrite <- Hi in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply between_expf_B0_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold p in |- *.
tauto.
assert (expf (B m zero x) xh0_1 t).
rewrite <- Hj in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply between_expf_B0_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold p in |- *.
tauto.
apply expf_trans with xh0_1.
apply expf_symm.
tauto.
tauto.
