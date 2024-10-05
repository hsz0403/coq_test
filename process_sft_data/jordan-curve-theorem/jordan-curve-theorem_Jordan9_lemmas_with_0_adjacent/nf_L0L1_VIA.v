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
tauto.
