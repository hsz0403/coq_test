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
Admitted.

Lemma expf_L0_CN:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> expf (L m zero x y) z t -> let x0 := cA m zero x in let x_1 := cA_1 m one x in let y_0:= cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in (if expf_dec m x_1 y then betweenf m x_1 z y /\ betweenf m x_1 t y \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m z t \/ expf m z y /\ expf m t x0 \/ expf m t y /\ expf m z x0).
Proof.
intros.
unfold expf in H1.
unfold MF.expo in H1.
decompose [and] H1.
clear H1.
elim H5.
clear H5.
intros i Hi.
assert (MF.f = cF).
tauto.
rewrite H1 in Hi.
rewrite <- Hi.
elim (expf_dec m x_1 y).
unfold y_0_1 in |- *.
unfold y_0 in |- *.
unfold x0 in |- *.
unfold x_1 in |- *.
apply expf_L0_CN_1.
tauto.
tauto.
intro.
unfold x0 in |- *.
apply expf_L0_CN_2.
tauto.
tauto.
Admitted.

Theorem expf_L0_CNS:forall (m:fmap)(x y z t:dart), inv_hmap (L m zero x y) -> exd m z -> (expf (L m zero x y) z t <-> let x0 := cA m zero x in let x_1 := cA_1 m one x in let y_0:= cA_1 m zero y in let y_0_1 := cA_1 m one y_0 in (if expf_dec m x_1 y then betweenf m x_1 z y /\ betweenf m x_1 t y \/ betweenf m y_0_1 z x0 /\ betweenf m y_0_1 t x0 \/ ~ expf m x_1 z /\ expf m z t else expf m z t \/ expf m z y /\ expf m t x0 \/ expf m t y /\ expf m z x0)).
Proof.
intros.
split.
intro.
apply expf_L0_CN.
tauto.
tauto.
tauto.
intro.
apply expf_L0_CS.
tauto.
tauto.
simpl in H1.
generalize H1.
elim (expf_dec m (cA_1 m one x) y).
tauto.
clear H1.
intros.
elim H1.
tauto.
clear H1.
intro.
elim H1.
clear H1.
intro.
right.
left.
split.
unfold expf in |- *.
split.
simpl in H.
tauto.
apply MF.expo_symm.
simpl in H.
tauto.
unfold expf in H1.
decompose [and] H1.
clear H1.
set (x0 := cA m zero x) in |- *.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
simpl in H.
unfold prec_L in H.
tauto.
rewrite H1 in |- *.
fold x0 in H6.
fold (cF m x0) in |- *.
assert (cF = MF.f).
tauto.
rewrite H3 in |- *.
unfold MF.expo in |- *.
unfold MF.expo in H6.
decompose [and] H6.
split.
tauto.
elim H8.
intros i Hi.
split with (S i).
simpl in |- *.
rewrite Hi in |- *.
tauto.
unfold expf in |- *.
unfold expf in H1.
split.
tauto.
apply MF.expo_symm.
tauto.
tauto.
clear H1.
left.
generalize H1.
unfold expf in |- *.
intros.
decompose [and] H2.
simpl in H.
unfold prec_L in H.
clear H2.
split.
split.
tauto.
apply MF.expo_symm.
tauto.
generalize H7.
clear H7.
unfold MF.expo in |- *.
intros.
split.
tauto.
decompose [and] H7.
elim H4.
intros i Hi.
split with (S i).
simpl in |- *.
set (x0 := cA m zero x) in |- *.
fold x0 in Hi.
assert (x = cA_1 m zero x0).
unfold x0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite Hi in |- *.
rewrite H8 in |- *.
fold (cF m x0) in |- *.
assert (cF = MF.f).
tauto.
rewrite H9 in |- *.
tauto.
split.
tauto.
apply MF.expo_symm.
tauto.
Admitted.

Lemma y_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> y = cA m1 zero x.
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec x x).
tauto.
Admitted.

Lemma x0_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> cA m zero x = bottom m1 zero x.
Proof.
simpl in |- *.
intros.
elim (eq_dart_dec y (bottom m zero x)).
intros.
unfold prec_L in H.
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
unfold prec_L in H.
intro.
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
Admitted.

Lemma x_1_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> cA_1 m one x = cA_1 m1 one x.
Proof.
simpl in |- *.
Admitted.

Lemma y_0_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> cA_1 m zero y = top m1 zero x.
Proof.
simpl in |- *.
unfold prec_L in |- *.
intros.
rewrite cA_1_top.
elim (eq_dart_dec x (top m zero x)).
tauto.
intro.
rewrite nosucc_top in b.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma y_0_1_L0:forall (m:fmap)(x y:dart), let m1 := L m zero x y in inv_hmap m1 -> cF m y = cA_1 m1 one (top m1 zero x).
Proof.
intros.
unfold cF in |- *.
unfold m1 in |- *.
rewrite <- y_0_L0.
simpl in |- *.
tauto.
fold m1 in |- *.
Admitted.

Lemma not_expf_expf_L0_CN: forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1:= cA_1 m one x in let x0 := cA m zero x in ~expf m x_1 y -> expf (L m zero x y) y x0.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
tauto.
rename H1 into Inv.
simpl in Inv.
unfold prec_L in Inv.
apply expf_L0_CS.
tauto.
tauto.
elim (expf_dec m (cA_1 m one x) y).
fold x_1 in |- *.
tauto.
fold x_1 in |- *.
intros.
right.
left.
split.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H1.
unfold cF in |- *.
unfold x_1 in |- *.
unfold x0 in |- *.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
unfold expf in |- *.
split.
tauto.
apply MF.expo_refl.
Admitted.

Lemma expf_not_expf_L0_CV:forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1:= cA_1 m one x in let x0 := cA m zero x in expf (L m zero x y) y x0 -> ~expf m x_1 y.
Proof.
intros.
assert (inv_hmap (L m zero x y)).
tauto.
rename H1 into Inv.
simpl in Inv.
unfold prec_L in Inv.
decompose [and] Inv.
clear Inv.
generalize (expf_L0_CN m x y y x0 H H2 H0).
simpl in |- *.
fold x_1 in |- *.
elim (expf_dec m x_1 y).
intros.
elim H6.
clear H6.
intros.
decompose [and] H6.
clear H6.
generalize H9.
clear H9.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim H9.
intros i Hi.
clear H9.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
set (p := MF.Iter_upb m x_1) in |- *.
fold p in H12.
assert (Iter (MF.f m) (p - 1) x_1 = x0).
rewrite <- MF.Iter_f_f_1.
unfold p in |- *.
rewrite MF.Iter_upb_period.
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H11.
unfold cF_1 in |- *.
unfold x_1 in |- *.
rewrite cA_cA_1.
fold x0 in |- *.
tauto.
tauto.
tauto.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
omega.
assert (i = (p - 1)%nat).
apply MF.unicity_mod_p with m x_1.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H6.
symmetry in |- *.
tauto.
absurd (i = (p - 1)%nat).
elim (eq_nat_dec i j).
intro.
rewrite a0 in H6.
assert (x0 = y).
rewrite <- H6.
tauto.
unfold x0 in H14.
tauto.
intro.
omega.
tauto.
tauto.
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
clear H6.
intro.
elim H6.
clear H6.
fold x0 in |- *.
fold (cF m y) in |- *.
intro.
decompose [and] H6.
clear H6.
assert (exd m x0).
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
generalize H8.
clear H8.
unfold betweenf in |- *.
unfold MF.between in |- *.
intros.
elim H8.
intros i Hi.
clear H8.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
set (y_0_1 := cF m y) in |- *.
fold y_0_1 in H8.
fold y_0_1 in H12.
set (p := MF.Iter_upb m (cF m y)) in |- *.
fold p in H14.
fold y_0_1 in p.
assert (Iter (MF.f m) (p - 1) y_0_1 = y).
rewrite <- MF.Iter_f_f_1.
unfold p in |- *.
rewrite MF.Iter_upb_period.
simpl in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H13.
unfold cF_1 in |- *.
unfold y_0_1 in |- *.
unfold cF in |- *.
rewrite cA_cA_1.
rewrite cA_cA_1.
tauto.
tauto.
tauto.
tauto.
generalize (exd_cA_1 m zero y).
tauto.
tauto.
unfold y_0_1 in |- *.
generalize (exd_cF m y).
tauto.
tauto.
unfold y_0_1 in |- *.
generalize (exd_cF m y).
tauto.
omega.
assert (i = (p - 1)%nat).
apply MF.unicity_mod_p with m y_0_1.
tauto.
unfold y_0_1 in |- *.
generalize (exd_cF m y).
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H13.
tauto.
elim (eq_nat_dec i j).
intro.
rewrite a0 in H8.
rewrite H12 in H8.
unfold x0 in H8.
tauto.
intro.
elim b.
omega.
tauto.
generalize (exd_cF m y).
tauto.
clear H6.
tauto.
Admitted.

Theorem expf_not_expf_L0: forall (m:fmap)(x y:dart), inv_hmap (L m zero x y) -> let x_1:= cA_1 m one x in let x0 := cA m zero x in (expf m x_1 y <-> ~expf (L m zero x y) y x0).
Proof.
intros.
generalize (expf_not_expf_L0_CV m x y H).
simpl in |- *.
fold x0 in |- *.
fold x_1 in |- *.
intros.
generalize (not_expf_expf_L0_CN m x y H).
simpl in |- *.
fold x0 in |- *.
fold x_1 in |- *.
intro.
generalize (expf_dec m x_1 y).
tauto.
