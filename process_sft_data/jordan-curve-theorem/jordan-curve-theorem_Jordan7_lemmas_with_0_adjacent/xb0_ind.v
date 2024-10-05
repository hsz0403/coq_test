Require Export Jordan6.

Lemma xb0_ind:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in let p := MF.Iter_upb m xh0_1 in xb0 = Iter (cF m) (p-1)%nat xh0_1.
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
assert (exd m xb0).
unfold xb0 in |- *.
apply exd_bottom.
tauto.
tauto.
assert (exd m xh0_1).
unfold xh0_1 in |- *.
generalize (exd_cA_1 m one xh0).
tauto.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H5 in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite <- H6 in |- *.
rewrite H5 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold xh0_1 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
unfold xh0 in |- *.
unfold xb0 in |- *.
rewrite cA_top in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
generalize (MF.upb_pos m xh0_1 H4).
intro.
fold p in H5.
omega.
