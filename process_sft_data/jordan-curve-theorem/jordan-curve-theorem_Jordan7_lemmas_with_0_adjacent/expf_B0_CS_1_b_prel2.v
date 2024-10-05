Require Export Jordan6.

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
tauto.
