Require Export Jordan6.

Lemma expf_B0_CS_1_b:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let xb0 := bottom m zero x in let xh0 := top m zero x in let xh0_1 := cA_1 m one xh0 in expf m x0 xb0 -> (betweenf m xh0_1 z x0 /\ betweenf m xh0_1 t x0) -> expf (B m zero x) z t.
Proof.
intros.
assert (exd m z /\ exd m t).
unfold betweenf in H2.
unfold MF.between in H2.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m xh0).
unfold xh0 in |- *.
apply exd_top.
tauto.
apply succ_exd with zero.
tauto.
tauto.
assert (exd m xh0_1).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
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
generalize (MF.exd_Iter_f m i xh0_1).
tauto.
elim H6.
intros k Hk.
clear H6.
elim Hk.
clear Hk.
intros l Hl.
elim Hl.
clear Hl.
intros.
assert (exd m t).
rewrite <- H6 in |- *.
generalize (MF.exd_Iter_f m k xh0_1).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
apply expf_B0_CS_1_b_aux.
tauto.
tauto.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xb0 in |- *.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold x0 in |- *.
tauto.
