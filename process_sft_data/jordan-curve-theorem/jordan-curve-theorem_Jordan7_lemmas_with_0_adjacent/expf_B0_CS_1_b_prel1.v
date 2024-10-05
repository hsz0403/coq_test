Require Export Jordan6.

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
omega.
