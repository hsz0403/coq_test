Require Export Jordan6.

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
tauto.
