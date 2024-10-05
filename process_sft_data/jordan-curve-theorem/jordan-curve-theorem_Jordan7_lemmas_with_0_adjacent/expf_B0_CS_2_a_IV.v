Require Export Jordan6.

Lemma expf_B0_CS_2_a_IV:forall (m:fmap)(x z t:dart), inv_hmap m -> succ m zero x -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> expf m x_1 z -> expf m xh0_1 t -> expf (B m zero x) z t.
Proof.
intros.
assert (MF.expo1 m xh0_1 t).
generalize (MF.expo_expo1 m xh0_1 t H).
unfold expf in H3.
tauto.
assert (MF.expo1 m x_1 z).
generalize (MF.expo_expo1 m x_1 z H).
unfold expf in H2.
tauto.
unfold MF.expo1 in H4.
unfold MF.expo1 in H5.
elim H4.
intros.
clear H4.
elim H5.
intros.
clear H5.
clear H4.
set (p := MF.Iter_upb m xh0_1) in |- *.
fold p in H7.
set (q := MF.Iter_upb m x_1) in |- *.
fold q in H8.
elim H7.
clear H7.
intros i Hi.
elim H8.
intros j Hj.
clear H8.
elim Hi.
clear Hi.
intros Ci Hi.
elim Hj; clear Hj.
intros Cj Hj.
assert (expf (B m zero x) xh0_1 t).
rewrite <- Hi in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply between_expf_B0_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold p in |- *.
tauto.
assert (expf (B m zero x) x_1 z).
rewrite <- Hj in |- *.
unfold x_1 in |- *.
apply between_expf_B0_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold q in |- *.
tauto.
assert (x0 = Iter (cF m) (q - 1) x_1).
unfold x_1 in |- *.
unfold q in |- *.
unfold x_1 in |- *.
rewrite <- x0_ind in |- *.
fold x0 in |- *.
tauto.
tauto.
tauto.
assert (xb0 = Iter (cF m) (p - 1) xh0_1).
unfold p in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
rewrite <- xb0_ind in |- *.
fold xb0 in |- *.
tauto.
tauto.
tauto.
assert (expf (B m zero x) x_1 x0).
rewrite H7 in |- *.
unfold x_1 in |- *.
apply between_expf_B0_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold x_1 in |- *.
fold q in |- *.
omega.
assert (expf (B m zero x) xh0_1 xb0).
rewrite H8 in |- *.
unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply between_expf_B0_2.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
fold xh0 in |- *.
fold xh0_1 in |- *.
fold p in |- *.
omega.
assert (expf (B m zero x) xb0 x_1).
unfold xb0 in |- *.
unfold x_1 in |- *.
apply expf_B0_xb0_x_1.
tauto.
tauto.
fold x0 in |- *.
fold xb0 in |- *.
tauto.
assert (expf (B m zero x) x0 xh0_1).
unfold x0 in |- *; unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply expf_B0_x0_xh0_1.
tauto.
tauto.
fold xb0 in |- *.
fold x0 in |- *.
tauto.
apply expf_trans with xh0_1.
apply expf_trans with x0.
apply expf_trans with x_1.
apply expf_symm.
tauto.
tauto.
tauto.
tauto.
