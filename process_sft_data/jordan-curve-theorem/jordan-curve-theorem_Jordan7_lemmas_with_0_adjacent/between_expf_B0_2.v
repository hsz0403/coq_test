Require Export Jordan6.

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
tauto.
