Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Lemma nf_L0L1_VIA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
tauto.
clear H6.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in H4.
tauto.
rewrite H6 in H17.
rewrite H18 in H12.
assert (MF.f = cF).
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H19 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = y'0).
unfold y'0 in |- *.
rewrite <- H4 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H22 in H12.
assert (x_1 = y'_1).
unfold y'_1 in |- *.
rewrite <- H4 in |- *.
fold x_1 in |- *.
tauto.
rewrite <- H23 in H12.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
elim H0.
clear H0.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x' y x0).
intros.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_trans with x'.
apply expf_symm.
tauto.
tauto.
clear H12.
intro.
elim H0.
clear H0.
intro.
generalize (betweenf_expf m x_1 y x'10).
tauto.
clear H0.
intro.
absurd (expf m x' x').
tauto.
apply expf_refl.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_VIB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x <> y' -> y_0 = y' -> False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
tauto.
clear H6.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H6 in H17.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = y'_1).
unfold y_0_1 in |- *; rewrite Eqy in |- *.
fold y'_1 in |- *.
tauto.
rewrite <- H19 in H12.
rewrite <- H18 in H12.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H26 in H12.
rewrite <- H19 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
rewrite H27 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H28 in H12.
rewrite H28 in H17.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x_1 y y); elim H0.
generalize (betweenf_expf m x_1 y y).
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m y_0_1 y x0).
intro.
elim H0.
apply expf_trans with x0.
apply expf_symm; tauto; apply expf_trans with y_0_1.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
tauto.
clear H12.
intro.
rewrite <- H28 in H12.
absurd (expf m x' y_0_1).
tauto.
apply expf_trans with y.
rewrite H18 in |- *.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H26 in H12.
elim H0.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x' x_1 y).
intro.
apply expf_trans with x'.
apply expf_symm.
tauto.
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m y_0_1 x_1 x'10).
intro.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_VIC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
tauto.
clear H6.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
tauto.
fold y'0 in |- *.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (exd m y'_1).
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H25 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
rewrite H26 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H27 in H12.
rewrite H27 in H17.
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
elim H0.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x_1 y y'0).
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m y'_1 y x0).
intros.
apply expf_trans with y'_1.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
tauto.
intro.
clear H12.
absurd (expf m x_1 y'_1).
tauto.
rewrite <- H27 in |- *.
apply expf_trans with y'0.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H25 in H12.
elim H0.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x' x_1 y'0).
generalize (betweenf_expf m x' y y'0).
intros.
apply expf_trans with x'.
apply expf_symm.
tauto.
tauto.
clear H12.
intro.
elim H12.
intro.
generalize (betweenf_expf m y'_1 y x'10).
generalize (betweenf_expf m y'_1 x_1 x'10); intros.
apply expf_trans with y'_1.
apply expf_symm.
tauto.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_VI:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_VIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_VIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
Admitted.

Lemma nf_L0L1_VIIA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = y'0).
unfold y'0 in |- *.
rewrite <- H4 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H24 in H12.
assert (x_1 = y'_1).
unfold y'_1 in |- *.
rewrite <- H4 in |- *.
fold x_1 in |- *.
tauto.
rewrite <- H25 in H12.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in H4.
tauto.
rewrite H26 in H12.
elim H12.
clear H12.
intro.
elim H0.
generalize (betweenf_expf m x' y x0).
intro.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_trans with x'.
apply expf_symm.
tauto.
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x_1 y x'10).
tauto.
intro.
absurd (expf m x' x').
tauto.
apply expf_refl.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_VIIB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x <> y' -> y_0 = y' -> False.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H6 in H17.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = y'_1).
unfold y_0_1 in |- *; rewrite Eqy in |- *.
fold y'_1 in |- *.
tauto.
rewrite <- H19 in H12.
rewrite <- H18 in H12.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H26 in H12.
rewrite <- H19 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
rewrite H27 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H28 in H12.
rewrite H28 in H17.
elim H0.
elim H12; clear H12; intro.
generalize (betweenf_expf m x_1 y_0_1 y).
tauto.
elim H12.
clear H12; intro.
generalize (betweenf_expf m y_0_1 y x0).
intro.
apply expf_trans with y_0_1.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
tauto.
intro.
absurd (expf m x_1 y_0_1).
tauto.
rewrite <- H28 in |- *.
apply expf_trans with y.
rewrite H18 in |- *; tauto; apply expf_symm; tauto.
apply expf_symm; tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H26 in H12.
elim H0.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x' x_1 y).
intros.
apply expf_trans with x'.
apply expf_symm.
tauto.
tauto.
intro.
clear H12.
elim H27.
clear H27.
intro.
generalize (betweenf_expf m y_0_1 x_1 x'10).
intro.
apply expf_trans with y_0_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_VIIC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
tauto.
fold y'0 in |- *.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (exd m y'_1).
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H25 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
rewrite H26 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H27 in H12.
rewrite H27 in H17.
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
elim H0.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x_1 y y'0).
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m y'_1 y x0).
intros.
apply expf_trans with y'_1.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
tauto.
intro.
absurd (expf m x_1 y'_1).
tauto.
rewrite <- H27 in |- *.
apply expf_trans with y'0.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H25 in H12.
elim H0.
elim H12.
clear H12.
intro.
generalize (betweenf_expf m x' x_1 y'0).
generalize (betweenf_expf m x' y y'0).
intros.
apply expf_trans with x'.
apply expf_symm.
tauto.
tauto.
clear H12.
intro.
elim H12.
intro.
generalize (betweenf_expf m y'_1 y x'10).
generalize (betweenf_expf m y'_1 x_1 x'10); intros.
apply expf_trans with y'_1.
apply expf_symm.
tauto.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_VII:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_VIIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_VIIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
Admitted.

Lemma nf_L0L1_VIIIB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> x <> y' -> y_0 = y' -> False.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (~ (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H6 in H17.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = y'_1).
unfold y_0_1 in |- *; rewrite Eqy in |- *.
fold y'_1 in |- *.
tauto.
rewrite <- H19 in H12.
rewrite <- H18 in H12.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H26 in H12.
rewrite <- H19 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
rewrite H27 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H28 in H12.
rewrite H28 in H17.
assert (expf m x_1 x0).
apply expf_symm.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H26 in H12.
assert (expf m x' y /\ expf m x0 x0).
split.
rewrite H18 in |- *.
tauto.
apply expf_refl.
tauto.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
tauto.
Admitted.

Lemma nf_L0L1_VIIIC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (~ (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
tauto.
fold y'0 in |- *.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (exd m y'_1).
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H25 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
rewrite H26 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H27 in H12.
rewrite H27 in H17.
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
rewrite <- H27 in H17.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H25 in H12.
tauto.
Admitted.

Lemma nf_L0L1_VIII:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_VIIIA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_VIIIB m x y x' y' H H0 H1 H2 H3 b a).
intros.
Admitted.

Lemma nf_L0L1_IXA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> ~ expf m x' y'0 -> expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
tauto.
clear H6.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = y'0).
unfold y'0 in |- *.
rewrite <- H4 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H24 in H12.
assert (x_1 = y'_1).
unfold y'_1 in |- *.
rewrite <- H4 in |- *.
fold x_1 in |- *.
tauto.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in H4.
tauto.
rewrite H26 in H12.
rewrite <- H24 in H1.
elim H12.
clear H12.
elim H17.
tauto.
intro.
elim H12.
clear H12 H17.
intro.
left.
tauto.
clear H12.
intro.
Admitted.

Lemma nf_L0L1_IXB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> ~ expf m x' y'0 -> expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> x <> y' -> y_0 = y' -> False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
tauto.
clear H6.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H6 in H17.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = y'_1).
unfold y_0_1 in |- *; rewrite Eqy in |- *.
fold y'_1 in |- *.
tauto.
rewrite <- H18 in H12.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H26 in H12.
rewrite <- H19 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H28 in H12.
rewrite H28 in H17.
absurd (expf m y_0_1 y).
tauto.
apply expf_symm.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H26 in H12.
elim H12.
clear H12.
elim H17.
clear H17.
intro.
right.
left.
split.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
apply expf_refl.
tauto.
tauto.
clear H17.
intro.
elim H12.
clear H12.
intro.
absurd (expf m x' y).
rewrite H18 in |- *.
tauto.
tauto.
clear H12.
intro.
elim H0.
apply expf_trans with x0.
apply expf_symm.
tauto.
Admitted.

Lemma nf_L0L1_IXC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> ~ expf m x' y'0 -> expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (~ (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0).
tauto.
clear H6.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
tauto.
fold y'0 in |- *.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (exd m y'_1).
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H25 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H27 in H12.
rewrite H27 in H17.
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
rewrite H27 in H1.
elim H12.
clear H12.
elim H17.
clear H17.
tauto.
clear H17.
intro.
elim H12.
clear H12.
intro.
tauto.
clear H12.
intro.
left.
apply expf_trans with y'0.
apply expf_symm.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H25 in H12.
elim H12.
clear H12.
elim H17.
clear H17.
intro.
tauto.
clear H17.
intro.
elim H12.
clear H12.
intro.
right.
right.
split.
apply expf_symm.
tauto.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
clear H12.
intro.
right.
left.
split.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
apply expf_symm.
Admitted.

Lemma nf_L0L1_IX:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> ~ expf m x' y'0 -> expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_IXA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_IXB m x y x' y' H H0 H1 H2 H3 b a).
intros.
Admitted.

Lemma nf_L0L1_XA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = y'0).
unfold y'0 in |- *.
rewrite <- H4 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H24 in H12.
assert (x_1 = y'_1).
unfold y'_1 in |- *.
rewrite <- H4 in |- *.
fold x_1 in |- *.
tauto.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in H4.
tauto.
rewrite H26 in H12.
elim H17.
clear H17.
elim H12.
tauto.
intro.
elim H17.
clear H17.
intro.
elim H0.
apply expf_trans with x0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
clear H17.
intro.
right.
right.
split.
apply expf_refl.
tauto.
tauto.
Admitted.

Lemma nf_L0L1_XB:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x <> y' -> y_0 = y' -> False.
Proof.
intros.
rename H5 into Eqy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = x0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
fold x0 in |- *.
tauto.
tauto.
rewrite H6 in H17.
assert (y = y'0).
unfold y'0 in |- *.
rewrite <- Eqy in |- *.
unfold y_0 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y_0_1 = y'_1).
unfold y_0_1 in |- *; rewrite Eqy in |- *.
fold y'_1 in |- *.
tauto.
rewrite <- H18 in H12.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H23 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H26 in H12.
rewrite <- H19 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H28 in H12.
rewrite H28 in H17.
elim H17.
left.
apply expf_symm.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H26 in H12.
elim H17.
clear H17.
elim H12.
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
left.
apply expf_trans with x_1.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
clear H12.
intro.
right.
left.
split.
apply expf_symm.
tauto.
apply expf_refl.
tauto.
unfold x0 in |- *.
generalize (exd_cA m zero x).
Admitted.

Lemma nf_L0L1_XC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> expf (L m one x' y') x_1b y -> x <> y' -> y_0 <> y' -> False.
Proof.
intros.
rename H5 into Dy.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
tauto.
intros.
clear b.
assert (expf m x_1b y \/ expf m x_1b x' /\ expf m y y'0 \/ expf m y x' /\ expf m x_1b y'0).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = y'0).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
fold y_0 in |- *.
elim (eq_dart_dec y_0 y').
tauto.
fold y'0 in |- *.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (exd m y'_1).
unfold y'_1 in |- *.
generalize (exd_cA_1 m one y').
tauto.
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H25 in H12.
assert (x'10 = x0).
unfold x'10 in |- *.
rewrite a in |- *.
fold x0 in |- *.
tauto.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H27 in H12.
rewrite H27 in H17.
assert (expf m y'0 y'_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
unfold y'0 in |- *.
generalize (exd_cA m zero y').
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y'0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
elim H17.
clear H17.
elim H12.
clear H12.
intro.
right.
right.
split.
apply expf_trans with y'_1.
tauto.
tauto.
apply expf_symm.
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
right.
right.
split.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
clear H12.
intro.
elim H0.
apply expf_symm.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a.
tauto.
fold x'1 in |- *.
fold x_1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
tauto.
rewrite H25 in H12.
elim H17.
clear H17.
elim H12.
tauto.
clear H12.
intro.
elim H12.
clear H12.
intro.
right.
right.
split.
apply expf_symm.
tauto.
apply expf_symm.
apply expf_trans with x_1.
tauto.
tauto.
clear H12.
intro.
right.
left.
split.
apply expf_symm.
tauto.
apply expf_trans with x_1.
apply expf_symm.
tauto.
apply expf_symm.
Admitted.

Lemma nf_L0L1_VIIIA:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in ~ expf m x_1 y -> expf m x' y'0 -> ~ expf (L m zero x y) x' y'0b -> ~ expf (L m one x' y') x_1b y -> x = y' -> False.
Proof.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L1.
fold m1 in |- *.
tauto.
set (x0 := cA m zero x) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (inv_hmap m).
tauto.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m y'0b).
unfold y'0b in |- *.
generalize (exd_cA (L m zero x y) zero y').
tauto.
assert (inv_hmap m2).
tauto.
unfold m2 in H12.
simpl in H12.
unfold prec_L in H12.
assert (exd m x').
tauto.
assert (exd m y').
tauto.
assert (inv_hmap (L m one x' y')).
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (exd m x_1b).
unfold x_1b in |- *.
generalize (exd_cA_1 (L m one x' y') one x).
tauto.
clear H6 H12.
generalize (expf_L1_CNS m x' y' x_1b y H15 H16).
simpl in |- *.
fold y'0 in |- *.
fold x'1 in |- *.
set (x'10 := cA m zero x'1) in |- *.
set (y'_1 := cA_1 m one y') in |- *.
elim (expf_dec m x' y'0).
intros.
clear a.
assert (~ (betweenf m x' x_1b y'0 /\ betweenf m x' y y'0 \/ betweenf m y'_1 x_1b x'10 /\ betweenf m y'_1 y x'10 \/ ~ expf m x' x_1b /\ expf m x_1b y)).
tauto.
clear H6.
generalize (expf_L0_CNS m x y x' y'0b H10 H13).
simpl in |- *.
fold x_1 in |- *.
fold y_0 in |- *.
fold x0 in |- *.
set (y_0_1 := cA_1 m one y_0) in |- *.
elim (expf_dec m x_1 y).
tauto.
intros.
clear b.
assert (~ (expf m x' y'0b \/ expf m x' y /\ expf m y'0b x0 \/ expf m y'0b y /\ expf m x' x0)).
tauto.
clear H6.
assert (y'0b = y).
unfold y'0b in |- *.
simpl in |- *.
elim (eq_dart_dec x y').
tauto.
tauto.
rewrite H6 in H17.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
assert (exd m y_0).
unfold y_0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
assert (exd m y_0_1).
unfold y_0_1 in |- *.
generalize (exd_cA_1 m one y_0).
tauto.
assert (MF.f = cF).
tauto.
assert (expf m x0 x_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x0 in |- *.
generalize (exd_cA m zero x).
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold x0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold x_1 in |- *.
tauto.
tauto.
tauto.
assert (expf m y y_0_1).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
rewrite H21 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (x0 = y'0).
unfold y'0 in |- *.
rewrite <- H4 in |- *.
fold x0 in |- *.
tauto.
rewrite <- H24 in H12.
assert (x_1 = y'_1).
unfold y'_1 in |- *.
rewrite <- H4 in |- *.
fold x_1 in |- *.
tauto.
rewrite <- H25 in H12.
assert (x_1b = x').
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
tauto.
intro.
symmetry in H4.
tauto.
rewrite H26 in H12.
elim H17.
right.
right.
split.
apply expf_refl.
tauto.
tauto.
rewrite H24 in |- *.
tauto.
tauto.
