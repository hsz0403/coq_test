Require Export Jordan6.

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
