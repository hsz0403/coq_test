Require Export Jordan6.

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
tauto.
