Require Export Jordan6.

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
tauto.
