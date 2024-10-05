Require Export Jordan7.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.

Lemma nf_L0L1_IVC:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> expf (L m zero x y) x' y'0b -> x <> y' -> y_0 <> y' -> False.
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
intros.
assert (betweenf m x_1 x' y /\ betweenf m x_1 y'0b y \/ betweenf m y_0_1 x' x0 /\ betweenf m y_0_1 y'0b x0 \/ ~ expf m x_1 x' /\ expf m x' y'0b).
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
elim (eq_dart_dec x'1 x).
intro.
assert (x_1b = y'_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a1.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
fold y'_1 in |- *.
tauto.
tauto.
rewrite H18 in H12.
assert (x' = x_1).
unfold x_1 in |- *.
rewrite <- a0 in |- *.
unfold x'1 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
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
rewrite H20 in |- *.
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
rewrite H20 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
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
rewrite H20 in |- *.
unfold cF in |- *.
unfold y'0 in |- *.
rewrite cA_1_cA in |- *.
fold y'_1 in |- *.
tauto.
tauto.
tauto.
elim H12.
clear H12.
elim H17.
clear H17.
intro.
generalize (betweenf_expf m x_1 y'0 y).
intros.
left.
apply expf_trans with y'0.
apply expf_symm.
tauto.
apply expf_trans with x_1.
apply expf_symm.
tauto.
tauto.
clear H17.
intro.
elim H12.
clear H12.
intro.
rewrite H19 in |- *.
rewrite H19 in H12.
right.
right.
split.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
intro.
rewrite <- H19 in H17.
absurd (expf m x' x').
tauto.
apply expf_refl.
tauto.
tauto.
intro.
assert (x_1b = x_1).
unfold x_1b in |- *.
simpl in |- *.
elim (eq_dart_dec y' x).
intro.
symmetry in a0.
tauto.
fold x'1 in |- *.
elim (eq_dart_dec x'1 x).
tauto.
fold x_1 in |- *.
tauto.
rewrite H18 in H12.
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
rewrite H6 in |- *.
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
rewrite H6 in |- *.
unfold y_0_1 in |- *.
unfold y_0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
tauto.
