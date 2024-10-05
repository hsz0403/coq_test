Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_L0_CN_2:forall (m:fmap)(x y z:dart)(i:nat), inv_hmap (L m zero x y) -> exd m z -> let x0 := cA m zero x in let x_1 := cA_1 m one x in let y_0:= cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in let t:= Iter (cF (L m zero x y)) i z in ~expf m x_1 y -> (expf m z t \/ expf m z y /\ expf m t x0 \/ expf m t y /\ expf m z x0).
Proof.
assert (MF.f = cF).
tauto.
assert (MF.f_1 = cF_1).
tauto.
intros.
assert (inv_hmap (L m zero x y)).
tauto.
rename H3 into a.
simpl in H4.
unfold prec_L in H4.
decompose [and] H4.
clear H4.
assert (exd m x0).
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
induction i.
simpl in t.
unfold t in |- *.
left.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
tauto.
simpl in t.
set (zi := Iter (cF (L m zero x y)) i z) in |- *.
fold zi in t.
assert (t = cF (L m zero x y) zi).
unfold t in |- *.
tauto.
generalize H11.
rewrite cF_L.
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y zi).
intros.
fold x_1 in H12.
fold zi in IHi.
elim IHi.
clear IHi.
intro.
rewrite H12.
rewrite <- a0 in H13.
right.
left.
split.
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA.
fold x_1 in |- *.
tauto.
tauto.
tauto.
rewrite H12.
clear IHi.
intro.
elim H13.
clear H13.
rewrite <- a0.
intro.
absurd (expf m x_1 y).
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with x0.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA.
fold x_1 in |- *.
tauto.
tauto.
tauto.
apply MF.expo_symm.
tauto.
unfold expf in H13.
tauto.
clear H13.
intro.
rewrite <- a0 in H13.
left.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with x0.
unfold expf in H13.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
unfold cF in |- *.
unfold x0 in |- *.
rewrite cA_1_cA.
fold x_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA m zero x) zi).
fold (cF m y) in |- *.
fold x0 in |- *.
intros.
rewrite H12.
fold zi in IHi.
simpl in IHi.
rewrite <- a0 in IHi.
elim IHi.
clear IHi.
intro.
right.
right.
split.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
tauto.
tauto.
clear IHi.
intros.
elim H13.
intro.
clear H13.
left.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with y.
unfold expf in H14.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
tauto.
clear H13.
intro.
right.
right.
split.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
tauto.
tauto.
intros.
fold (cF m zi) in H12.
fold zi in IHi.
simpl in IHi.
rewrite H12.
elim IHi.
clear IHi.
intro.
left.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with zi.
unfold expf in H13.
tauto.
unfold expf in |- *.
split.
apply MF.expo_exd with z.
tauto.
unfold expf in H13.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
tauto.
clear IHi.
intros.
elim H13.
clear H13.
intro.
right.
left.
split.
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with zi.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
unfold expf in H13.
unfold MF.expo in H13.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
tauto.
unfold expf in H13.
tauto.
clear H13.
intro.
right.
right.
split.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with zi.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
unfold expf in H13.
unfold MF.expo in H13.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H.
tauto.
unfold expf in H13.
tauto.
tauto.
tauto.
tauto.
simpl in H1.
tauto.
