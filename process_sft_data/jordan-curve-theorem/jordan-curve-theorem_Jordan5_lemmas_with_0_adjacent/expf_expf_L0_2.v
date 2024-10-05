Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_expf_L0_2:forall (m:fmap)(x y z:dart)(i:nat), inv_hmap (L m zero x y) -> exd m z -> let x_1 := cA_1 m one x in ~ expf m x_1 y -> ~ expf m x_1 z -> ~ expf m y z -> let t:= Iter (cF m) i z in expf (L m zero x y) z t.
Proof.
assert (MF.f = cF).
tauto.
rename H into Ef.
intros.
assert (inv_hmap (L m zero x y)).
tauto.
simpl in H4.
unfold prec_L in H4.
decompose [and] H4.
clear H4.
induction i.
simpl in t.
unfold t in |- *.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
simpl in |- *.
tauto.
simpl in t.
set (zi := Iter (cF m) i z) in |- *.
fold zi in t.
fold zi in IHi.
simpl in IHi.
unfold expf in |- *.
split.
tauto.
unfold expf in IHi.
apply MF.expo_trans with zi.
tauto.
unfold t in |- *.
assert (prec_L m zero x y).
simpl in H.
tauto.
generalize (cF_L m zero x y zi H5 H4).
elim (eq_dim_dec zero zero).
elim (eq_dart_dec y zi).
intros.
rewrite a in H3.
elim H3.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
rewrite Ef.
tauto.
elim (eq_dart_dec (cA m zero x) zi).
intros.
assert (x = cA_1 m zero zi).
rewrite <- a.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
assert (x_1 = t).
unfold t in |- *.
unfold cF in |- *.
rewrite <- a.
rewrite cA_1_cA.
unfold x_1 in |- *.
tauto.
tauto.
tauto.
elim H2.
rewrite H13.
unfold t in |- *.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
tauto.
rewrite Ef.
unfold zi in |- *.
split with (S i).
simpl in |- *.
tauto.
intros.
unfold cF in |- *.
rewrite <- H10.
unfold MF.expo in |- *.
split.
simpl in |- *.
unfold zi in |- *.
generalize (MF.exd_Iter_f m i z).
tauto.
split with 1%nat.
simpl in |- *.
rewrite Ef.
tauto.
tauto.
