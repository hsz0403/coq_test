Require Export Jordan6.

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
tauto.
