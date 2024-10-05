Require Export Jordan6.

Lemma expf_B0_CS_1_a:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let x_1 := cA_1 m one x in expf m x0 xb0 -> (betweenf m x_1 z xb0 /\ betweenf m x_1 t xb0) -> expf (B m zero x) z t.
Proof.
intros.
assert (exd m z /\ exd m t).
unfold betweenf in H2.
unfold MF.between in H2.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
elim H2.
clear H2.
intros.
elim H2.
intros i Hi.
elim Hi.
intros j Hj.
clear Hi.
clear H2.
elim Hj.
clear Hj.
intros.
assert (exd m z).
rewrite <- H2 in |- *.
generalize (MF.exd_Iter_f m i x_1).
tauto.
elim H5.
intros k Hk.
clear H5.
elim Hk.
clear Hk.
intros l Hl.
elim Hl.
clear Hl.
intros.
assert (exd m t).
rewrite <- H5 in |- *.
generalize (MF.exd_Iter_f m k x_1).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
apply expf_B0_CS_1_a_aux.
tauto.
tauto.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold xb0 in |- *.
tauto.
