Require Export Jordan6.

Lemma expf_B0_CS_1_a_prel2:forall (m:fmap)(x z:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in expf m x0 xb0 -> betweenf m x_1 z xb0 -> expf (B m zero x) x_1 z.
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
unfold x_1 in |- *.
decompose [and] Hj.
clear Hj.
rewrite <- H2.
unfold x_1 in |- *.
apply (expf_B0_CS_1_a_prel1 m x i j).
tauto.
tauto.
fold xb0 in |- *.
fold x_1 in |- *.
symmetry in |- *.
tauto.
fold x_1 in |- *.
omega.
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
