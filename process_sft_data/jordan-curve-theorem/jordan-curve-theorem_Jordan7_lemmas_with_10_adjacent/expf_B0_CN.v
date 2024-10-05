Require Export Jordan6.

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

Lemma betweenf1 : forall(m:fmap)(u v u' v':dart), inv_hmap m -> exd m u' -> u <> u' -> v <> v' -> (betweenf m u' u v' /\ betweenf m u' v v') -> (betweenf m u u' v /\ betweenf m u v' v \/ betweenf m (cF m v) u' (cF_1 m u) /\ betweenf m (cF m v) v' (cF_1 m u)).
Proof.
intros.
assert (betweenf m u' u v' /\ betweenf m u' v v').
tauto.
rename H4 into H3'.
unfold betweenf in H3.
unfold MF.between in H3.
decompose [and] H3.
clear H3.
generalize (H4 H H0).
clear H4.
intro.
generalize (H5 H H0).
clear H5.
intros.
elim H3.
clear H3.
intros iu Hiu.
elim Hiu.
clear Hiu.
intros jv' Hiv'.
decompose [and] Hiv'.
clear Hiv'.
elim H4.
clear H4.
intros iv Hiv.
elim Hiv.
clear Hiv.
intros jv'1 Hjv.
decompose [and] Hjv.
clear Hjv.
set (p := MF.Iter_upb m u') in |- *.
fold p in H11.
fold p in H8.
decompose [and] H3'.
clear H3'.
unfold betweenf in H10.
generalize (MF.between_expo m u' u v' H H0 H10).
intro.
unfold betweenf in H12.
generalize (MF.between_expo m u' v v' H H0 H12).
intro.
decompose [and] H13.
decompose [and] H14.
clear H13 H14.
assert (MF.f = cF).
tauto.
assert (MF.expo m u' (cF m v)).
apply MF.expo_trans with v.
tauto.
assert (exd m v).
generalize (MF.expo_exd m u' v).
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
tauto.
generalize (MF.period_expo m u' u H H15).
intro.
generalize (MF.period_expo m u' (cF m v) H H14).
intro.
fold p in H19.
fold p in H20.
assert (jv' = jv'1).
apply (MF.unicity_mod_p m u').
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
tauto.
rewrite H6 in |- *.
rewrite H9 in |- *.
tauto.
assert (iu <> 0%nat).
intro.
rewrite H22 in H3.
simpl in H3.
symmetry in H3.
tauto.
assert (iv <> jv').
intro.
rewrite <- H21 in H9.
rewrite <- H23 in H9.
rewrite H4 in H9.
tauto.
assert (exd m (cF m v)).
generalize (MF.expo_exd m u' v).
generalize (exd_cF m v).
tauto.
elim (le_gt_dec iu iv).
intro.
right.
split.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (p - S iv)%nat.
split with (p - S iv + (iu - 1))%nat.
rewrite <- H20 in |- *.
split.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H20 in |- *.
rewrite MF.Iter_upb_period in |- *.
rewrite MF.Iter_f_1_Si in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite <- H27 in |- *.
rewrite cF_1_cF in |- *.
rewrite <- H4 in |- *.
apply MF.Iter_f_f_1_i.
tauto.
tauto.
tauto.
generalize (exd_cF m v).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
assert (cF_1 = MF.f_1).
tauto.
assert ((p - S iv + (iu - 1))%nat = (p + iu - 1 - S iv)%nat).
omega.
rewrite H28 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite MF.Iter_f_1_Si in |- *.
rewrite <- H13 in |- *.
assert (MF.f m v = Iter (MF.f m) 1 v).
simpl in |- *.
tauto.
rewrite H29 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p + iu - 1 + 1)%nat = S (p + iu - 1)).
omega.
rewrite H30 in |- *.
rewrite MF.f_1_Iter_f in |- *.
rewrite MF.Iter_f_f_1 in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p + iu - 1 - iv + iv)%nat = (p + iu - 1)%nat).
clear H28 H30.
omega.
rewrite H31 in |- *.
rewrite <- H3 in |- *.
assert ((p + iu - 1)%nat = (p + (iu - 1))%nat).
clear H30 H31 H28.
omega.
rewrite H32 in |- *.
rewrite MF.Iter_plus_inv in |- *.
assert (iu = S (iu - 1)).
clear H30 H31 H32.
omega.
rewrite H33 in |- *.
rewrite MF.f_1_Iter_f in |- *.
rewrite <- H33 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
tauto.
generalize (exd_cF m v).
tauto.
clear H28 H30.
omega.
tauto.
generalize (exd_cF m v).
tauto.
tauto.
generalize (MF.exd_Iter_f m (p + iu - 1) (cF m v)).
tauto.
tauto.
tauto.
clear H28.
omega.
omega.
assert (cF_1 = MF.f_1).
tauto.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (jv' - S iv)%nat.
split with (p - S iv + (iu - 1))%nat.
rewrite <- H20 in |- *.
split.
rewrite <- H13 in |- *.
assert (MF.f m v = Iter (MF.f m) 1 v).
simpl in |- *.
tauto.
rewrite H28 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H9 in |- *.
rewrite <- H21 in |- *.
assert ((jv' - S iv + 1 + iv)%nat = jv').
omega.
rewrite H29 in |- *.
tauto.
split.
rewrite <- H13 in |- *.
assert (MF.f m v = Iter (MF.f m) 1 v).
simpl in |- *.
tauto.
rewrite H28 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H3 in |- *.
rewrite H25 in |- *.
assert (iu = S (iu - 1)).
omega.
rewrite H29 in |- *.
rewrite MF.f_1_Iter_f in |- *.
assert ((p - S iv + (S (iu - 1) - 1) + 1 + iv)%nat = (p + (iu - 1))%nat).
clear H29.
omega.
rewrite H30 in |- *.
apply MF.Iter_plus_inv.
tauto.
tauto.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
tauto.
tauto.
omega.
intro.
left.
split.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (p - iu)%nat.
split with (p + iv - iu)%nat.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - iu + iu)%nat = p).
omega.
rewrite H27 in |- *.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
split.
rewrite <- H3 in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p + iv - iu + iu)%nat = (p + iv)%nat).
omega.
rewrite H27 in |- *.
apply MF.Iter_plus_inv.
tauto.
tauto.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
fold p in |- *.
rewrite <- H19 in |- *.
omega.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
split with (jv' - iu)%nat.
split with (p - iu + iv)%nat.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H6 in |- *.
assert ((jv' - iu + iu)%nat = jv').
omega.
rewrite H27 in |- *.
tauto.
split.
rewrite <- H3 in |- *.
rewrite <- H4 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - iu + iv + iu)%nat = (p + iv)%nat).
omega.
rewrite H27 in |- *.
apply MF.Iter_plus_inv.
tauto.
tauto.
unfold p in |- *.
apply MF.Iter_upb_period.
tauto.
tauto.
Admitted.

Lemma betweenf2:forall(m:fmap)(u v u' v':dart), inv_hmap m -> exd m v' -> u <> u' -> v <> v' -> (betweenf m (cF m v') u (cF_1 m u') /\ betweenf m (cF m v') v (cF_1 m u')) -> (betweenf m u u' v /\ betweenf m u v' v \/ betweenf m (cF m v) u' (cF_1 m u) /\ betweenf m (cF m v) v' (cF_1 m u)).
Proof.
intros.
assert (betweenf m (cF m v') u (cF_1 m u') /\ betweenf m (cF m v') v (cF_1 m u')).
tauto.
rename H4 into H3'.
unfold betweenf in H3.
unfold MF.between in H3.
decompose [and] H3.
clear H3.
assert (exd m (cF m v')).
generalize (exd_cF m v').
tauto.
rename H3 into Ev'1.
generalize (H4 H Ev'1).
clear H4.
intro.
generalize (H5 H Ev'1).
clear H5.
intros.
elim H3.
clear H3.
intros iu Hiu.
elim Hiu.
clear Hiu.
intros iu'_1 Hiu'_1.
decompose [and] Hiu'_1.
clear Hiu'_1.
elim H4.
clear H4.
intros iv Hiv.
elim Hiv.
clear Hiv.
intros iu'_2 Hiu'_2.
decompose [and] Hiu'_2.
clear Hiu'_2.
set (p := MF.Iter_upb m (cF m v')) in |- *.
fold p in H11.
fold p in H8.
decompose [and] H3'.
clear H3'.
unfold betweenf in H10.
generalize (MF.between_expo m (cF m v') u (cF_1 m u') H Ev'1 H10).
intro.
unfold betweenf in H12.
generalize (MF.between_expo m (cF m v') v (cF_1 m u') H Ev'1 H12).
intro.
decompose [and] H13.
decompose [and] H14.
clear H13 H14.
assert (MF.f = cF).
tauto.
assert (iu'_1 = iu'_2).
apply (MF.unicity_mod_p m (cF m v')).
tauto.
tauto.
fold p in |- *.
tauto.
fold p in |- *.
tauto.
rewrite H9 in |- *.
tauto.
rewrite <- H14 in H7.
clear H11 H9 H14.
clear iu'_2.
assert (MF.f_1 = cF_1).
tauto.
elim (eq_nat_dec (p - 1) iv).
intro.
assert (v' = Iter (MF.f m) (p - 1) (cF m v')).
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (exd_cF_1 m v').
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
symmetry in H9.
rewrite a in H11.
rewrite H4 in H11.
symmetry in H11.
tauto.
intro.
assert (exd m (cF_1 m u')).
rewrite <- H6 in |- *.
generalize (MF.exd_Iter_f m iu'_1 (cF m v')).
tauto.
assert (exd m u').
generalize (exd_cF_1 m u').
tauto.
elim (eq_nat_dec (S iu'_1) iu).
intro.
assert (Iter (MF.f m) (S iu'_1) (cF m v') = u').
simpl in |- *.
rewrite H6 in |- *.
rewrite H13 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite a in H19.
rewrite H3 in H19.
tauto.
intro.
set (v'1 := cF m v') in |- *.
fold v'1 in Ev'1.
fold v'1 in H3.
fold v'1 in H6.
fold v'1 in H4.
fold v'1 in p.
fold v'1 in H10.
fold v'1 in H12.
fold v'1 in H15.
fold v'1 in H16.
fold v'1 in H17.
fold v'1 in H18.
set (u'_1 := cF_1 m u') in |- *.
fold u'_1 in H6.
fold u'_1 in H10.
fold u'_1 in H12.
fold u'_1 in H16.
fold u'_1 in H18.
fold u'_1 in H11.
assert (exd m v).
apply MF.expo_exd with v'1.
tauto.
tauto.
assert (exd m (cF m v)).
generalize (exd_cF m v).
tauto.
set (v1 := cF m v) in |- *.
set (u_1 := cF_1 m u) in |- *.
assert (MF.expo m v'1 v1).
apply MF.expo_trans with v.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
unfold v1 in |- *.
tauto.
assert (p = MF.Iter_upb m v1).
unfold MF.expo in H21.
elim H21.
clear H21.
intros.
elim H22.
intros i Hi.
rewrite <- Hi in |- *.
unfold p in |- *.
apply MF.period_uniform.
tauto.
tauto.
elim (le_gt_dec iu iv).
intro.
right.
split.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim (eq_nat_dec iu'_1 (p - 1)).
intro.
assert (u' = v'1).
assert (u' = cF m u'_1).
unfold u'_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite H25 in |- *.
rewrite <- H6 in |- *.
rewrite a0 in |- *.
assert (cF m (Iter (MF.f m) (p - 1) v'1) = Iter (MF.f m) 1 (Iter (MF.f m) (p - 1) v'1)).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H26 in |- *.
clear H26.
rewrite <- MF.Iter_comp in |- *.
assert ((1 + (p - 1))%nat = p).
omega.
rewrite H26 in |- *.
clear H26.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
assert (u <> v'1).
intro.
rewrite <- H25 in H26.
tauto.
assert (iu <> 0%nat).
intro.
rewrite H27 in H3.
simpl in H3.
symmetry in H3.
tauto.
clear H23.
clear H26.
split with (p - S iv)%nat.
split with (p - S iv + iu - 1)%nat.
rewrite <- H22 in |- *.
split.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H22 in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold v1 in |- *.
rewrite <- H4 in |- *.
simpl in |- *.
rewrite H9 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H23 in |- *.
assert (cF_1 m (Iter (cF_1 m) iv (Iter (MF.f m) (S iv) v'1)) = Iter (cF_1 m) (S iv) (Iter (MF.f m) (S iv) v'1)).
simpl in |- *.
tauto.
rewrite H26 in |- *.
rewrite <- H9 in |- *.
rewrite MF.Iter_f_f_1_i in |- *.
assert (u' = cF m u'_1).
unfold u'_1 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite H28 in |- *.
rewrite <- H6 in |- *.
rewrite a0 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite <- H13 in |- *.
rewrite MF.f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
tauto.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv + iu - 1 + S iv)%nat = (iu - 1 + p)%nat).
omega.
rewrite H26 in |- *.
clear H26.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H3 in |- *.
simpl in |- *.
unfold u_1 in |- *.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
omega.
intro.
elim (eq_nat_dec iu 0).
intro.
assert (u = v'1).
rewrite a0 in H3.
simpl in H3.
symmetry in |- *.
tauto.
split with (S iu'_1 - S iv)%nat.
split with (p - S iv - 1)%nat.
rewrite <- H22 in |- *.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H26 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((S iu'_1 - S iv + S iv)%nat = S iu'_1).
omega.
rewrite H27 in |- *.
clear H27 H26.
simpl in |- *.
rewrite H6 in |- *.
unfold u'_1 in |- *.
rewrite H13 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H26 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv - 1 + S iv)%nat = (p - 1)%nat).
omega.
rewrite H27 in |- *.
clear H27.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
rewrite <- H25 in |- *.
unfold u_1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
omega.
intro.
split with (S iu'_1 - S iv)%nat.
split with (p - S iv + iu - 1)%nat.
rewrite <- H22 in |- *.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H25 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((S iu'_1 - S iv + S iv)%nat = S iu'_1).
omega.
rewrite H26 in |- *.
clear H25 H26.
simpl in |- *.
rewrite H6 in |- *.
unfold u'_1 in |- *.
rewrite H13 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
split.
unfold v1 in |- *.
rewrite <- H4 in |- *.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H25 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv + iu - 1 + S iv)%nat = (iu - 1 + p)%nat).
omega.
rewrite H26 in |- *.
clear H26.
clear H25.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H3 in |- *.
simpl in |- *.
unfold u_1 in |- *.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
omega.
assert (cF m (Iter (MF.f m) iv v'1) = Iter (MF.f m) (S iv) v'1).
simpl in |- *.
rewrite H13 in |- *.
tauto.
rewrite H4 in H23.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear H24.
rewrite <- H22 in |- *.
elim (eq_nat_dec iu 0).
split with (p - 1 - S iv)%nat.
split with (p - S iv - 1)%nat.
split.
unfold v1 in |- *.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - 1 - S iv + S iv)%nat = (p - 1)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold v'1 in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (exd_cF m v').
fold v'1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
unfold v1 in |- *.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv - 1 + S iv)%nat = (p - 1)%nat).
omega.
rewrite H24 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold v'1 in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
rewrite a0 in H3.
simpl in H3.
unfold u_1 in |- *.
rewrite <- H3 in |- *.
unfold v'1 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
omega.
intro.
split with (p - 1 - S iv)%nat.
split with (p - S iv + iu - 1)%nat.
split.
unfold v1 in |- *.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - 1 - S iv + S iv)%nat = (p - 1)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold v'1 in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (exd_cF m v').
fold v'1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
unfold v1 in |- *.
rewrite H23 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - S iv + iu - 1 + S iv)%nat = (p + (iu - 1))%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite H3 in |- *.
simpl in |- *.
unfold u_1 in |- *.
tauto.
tauto.
tauto.
omega.
tauto.
tauto.
omega.
intro.
left.
unfold betweenf in |- *.
assert (p = MF.Iter_upb m u).
rewrite <- H3 in |- *.
unfold p in |- *.
apply MF.period_uniform.
tauto.
tauto.
split.
unfold MF.between in |- *.
intros.
clear H24.
split with (iu'_1 + 1 - iu)%nat.
split with (p + iv - iu)%nat.
rewrite <- H23 in |- *.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((iu'_1 + 1 - iu + iu)%nat = S iu'_1).
omega.
rewrite H24 in |- *.
clear H24.
simpl in |- *.
rewrite H6 in |- *.
unfold u'_1 in |- *.
rewrite H13 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p + iv - iu + iu)%nat = (iv + p)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
tauto.
omega.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
clear H24.
split with (p - 1 - iu)%nat.
split with (p - iu + iv)%nat.
rewrite <- H23 in |- *.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - 1 - iu + iu)%nat = (p - 1)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold v'1 in |- *.
rewrite H9 in |- *.
rewrite cF_1_cF in |- *.
tauto.
tauto.
generalize (exd_cF m v').
fold v'1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
split.
rewrite <- H3 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert ((p - iu + iv + iu)%nat = (p + iv)%nat).
omega.
rewrite H24 in |- *.
clear H24.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
tauto.
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
tauto.
