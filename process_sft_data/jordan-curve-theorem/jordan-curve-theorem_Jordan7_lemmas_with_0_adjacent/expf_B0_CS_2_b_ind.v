Require Export Jordan6.

Lemma expf_B0_CS_2_b_ind:forall (m:fmap)(x z:dart)(i:nat), inv_hmap m -> succ m zero x -> exd m z -> let x0 := cA m zero x in let x_1:= cA_1 m one x in let xb0:= bottom m zero x in let xh0:= top m zero x in let xh0_1:= cA_1 m one xh0 in ~expf m x0 xb0 -> let t:=Iter (cF m) i z in ~expf m x_1 z -> ~expf m xh0_1 z -> expf (B m zero x) z t.
Proof.
intros.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
assert (exd (B m zero x) z).
generalize (exd_B m zero x z).
tauto.
assert (MF.f = cF).
tauto.
induction i.
simpl in t.
unfold t in |- *.
apply expf_refl.
tauto.
tauto.
simpl in t.
set (zi := Iter (cF m) i z) in |- *.
simpl in IHi.
fold zi in IHi.
unfold t in |- *.
fold zi in |- *.
apply expf_trans with zi.
tauto.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
assert (exd m zi).
unfold zi in |- *.
generalize (MF.exd_Iter_f m i z).
tauto.
assert (exd (B m zero x) zi).
generalize (exd_B m zero x zi).
tauto.
split.
tauto.
rewrite H7 in |- *.
split with 1%nat.
simpl in |- *.
rewrite cF_B in |- *.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec (A m zero x) zi).
intros.
assert (cA m zero x = A m zero x).
rewrite cA_eq in |- *.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
clear a0.
fold x0 in H10.
rewrite a in H10.
assert (expf m z zi).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
rewrite H7 in |- *.
tauto.
absurd (expf m x_1 z).
tauto.
apply expf_trans with x0.
apply expf_symm.
unfold x0 in |- *.
unfold x_1 in |- *.
apply expf_x0_x_1.
tauto.
apply succ_exd with zero.
tauto.
tauto.
rewrite H10 in |- *.
apply expf_symm.
tauto.
elim (eq_dart_dec (bottom m zero x) zi).
intros.
rewrite cA_1_B_ter in |- *.
fold xb0 in a.
assert (expf m z zi).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
rewrite H7 in |- *.
tauto.
absurd (expf m xh0_1 z).
tauto.
apply expf_trans with xb0.
apply expf_symm.
unfold xb0 in |- *; unfold xh0_1 in |- *.
unfold xh0 in |- *.
apply expf_xb0_xh0_1.
tauto.
apply succ_exd with zero.
tauto.
tauto.
apply expf_trans with zi.
rewrite a in |- *.
apply expf_refl.
tauto.
tauto.
apply expf_symm.
tauto.
tauto.
intro.
inversion H10.
rewrite cA_1_B_ter in |- *.
unfold cF in |- *.
tauto.
tauto.
intro.
inversion H10.
tauto.
tauto.
tauto.
