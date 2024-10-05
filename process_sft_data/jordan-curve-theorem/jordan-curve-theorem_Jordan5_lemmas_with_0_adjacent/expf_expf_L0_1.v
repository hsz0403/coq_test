Require Export Jordan4.
Definition betweenf:= MF.between.

Lemma expf_expf_L0_1:forall (m:fmap)(x y z:dart)(i:nat), inv_hmap (L m zero x y) -> exd m z -> let x_1 := cA_1 m one x in let t := Iter (cF m) i z in expf m x_1 y -> ~ expf m x_1 z -> expf (L m zero x y) z t.
Proof.
intros.
induction i.
simpl in t.
unfold t in |- *.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
simpl in |- *.
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_trans with (Iter (cF m) i z).
simpl in IHi.
unfold expf in IHi.
tauto.
simpl in t.
set (zi := Iter (cF m) i z) in |- *.
fold zi in t.
unfold t in |- *.
assert (MF.f = cF).
tauto.
assert (cF (L m zero x y) zi = cF m zi).
rewrite cF_L.
elim (eq_dim_dec zero zero).
intro.
elim (eq_dart_dec y zi).
intro.
rewrite a0 in H1.
elim H2.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_trans with zi.
unfold expf in H1.
tauto.
apply MF.expo_symm.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
tauto.
intro.
elim (eq_dart_dec (cA m zero x) zi).
intro.
assert (expf m x_1 zi).
rewrite <- a0.
unfold x_1 in |- *.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_symm.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
simpl in H.
unfold prec_L in H.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H4.
unfold cF in |- *.
rewrite cA_1_cA.
tauto.
simpl in H.
tauto.
unfold prec_L in H.
simpl in H.
unfold prec_L in H.
tauto.
assert (expf m z zi).
unfold zi in |- *.
unfold expf in |- *.
split.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
rewrite H3.
tauto.
elim H2.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_trans with zi.
unfold expf in H4.
tauto.
apply MF.expo_symm.
simpl in H.
tauto.
unfold expf in H5.
tauto.
unfold cF in |- *.
tauto.
tauto.
simpl in H.
tauto.
simpl in H.
tauto.
rewrite <- H4.
unfold MF.expo in |- *.
simpl in |- *.
split.
unfold zi in |- *.
generalize (MF.exd_Iter_f m i z).
rewrite H3.
simpl in H.
tauto.
split with 1%nat.
simpl in |- *.
rewrite H3.
tauto.
