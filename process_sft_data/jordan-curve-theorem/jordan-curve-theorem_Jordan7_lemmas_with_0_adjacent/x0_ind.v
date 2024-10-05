Require Export Jordan6.

Lemma x0_ind:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in let p := MF.Iter_upb m x_1 in x0 = Iter (cF m) (p-1)%nat x_1.
Proof.
intros.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
assert (exd m x0).
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (cF = MF.f).
tauto.
assert (cF_1 = MF.f_1).
tauto.
rewrite H4 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold x_1 in |- *.
rewrite <- H5 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
generalize (MF.upb_pos m x_1 H3).
fold p in |- *.
intro.
omega.
