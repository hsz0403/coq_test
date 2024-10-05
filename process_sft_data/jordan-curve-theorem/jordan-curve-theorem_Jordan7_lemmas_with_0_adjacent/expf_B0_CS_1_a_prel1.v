Require Export Jordan6.

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
omega.
