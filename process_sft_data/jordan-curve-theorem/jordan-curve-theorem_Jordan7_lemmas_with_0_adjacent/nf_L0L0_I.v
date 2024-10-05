Require Export Jordan6.

Lemma nf_L0L0_I:forall (m:fmap)(x y x' y':dart), let m1:= L (L m zero x y) zero x' y' in let m2:= L (L m zero x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let x'_1 := cA_1 m one x' in expf m x_1 y -> expf m x'_1 y' -> expf (L m zero x' y') x_1 y -> ~ expf (L m zero x y) x'_1 y' -> nf m1 = nf m2.
Proof.
intros.
rename H0 into E0.
rename H1 into E1.
rename H2 into E2.
rename H3 into E3.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L0.
fold m1 in |- *.
tauto.
unfold m1 in |- *.
unfold m2 in |- *.
simpl in |- *.
assert (inv_hmap m1).
tauto.
assert (inv_hmap m2).
tauto.
unfold m1 in H1.
unfold m2 in H2.
simpl in H1.
simpl in H2.
unfold prec_L in H1.
unfold prec_L in H2.
unfold pred in H1.
unfold pred in H2.
unfold succ in H1.
unfold succ in H2.
simpl in H1.
simpl in H2.
decompose [and] H1.
clear H1.
decompose [and] H2.
clear H2.
generalize H11 H14 H21 H24.
elim (eq_dart_dec x x').
intros.
elim H2.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec x' x).
intros.
elim H25.
apply exd_not_nil with m.
tauto.
auto.
clear H11 H14 H21 H24.
intros.
generalize H12 H22.
clear H12 H22.
elim (eq_dart_dec y y').
intros.
elim H12.
apply exd_not_nil with m.
tauto.
tauto.
elim (eq_dart_dec y' y).
intros.
elim H22.
apply exd_not_nil with m.
tauto.
tauto.
intros.
clear H13 H19 H1 H16.
clear H11 H21 H12 H22.
clear H15.
clear b0 b2.
set (xb0 := cA m zero x) in |- *.
fold xb0 in H14.
set (x'b0 := cA m zero x') in |- *.
fold x'b0 in H24.
set (yt0 := cA_1 m zero y) in |- *.
fold yt0 in H14.
set (y't0 := cA_1 m zero y') in |- *.
fold y't0 in H24.
assert (inv_hmap (L m zero x y)).
simpl in |- *.
unfold m1 in H.
simpl in H.
tauto.
assert (exd m x'_1).
unfold x'_1 in |- *.
generalize (exd_cA_1 m one x').
tauto.
assert (inv_hmap (L m zero x' y')).
simpl in |- *.
unfold m2 in H0.
simpl in H0.
tauto.
assert (exd m x_1).
unfold x_1 in |- *.
generalize (exd_cA_1 m one x).
tauto.
generalize (expf_L0_CNS m x y x'_1 y' H1 H2).
simpl in |- *.
fold x_1 in |- *.
fold xb0 in |- *.
fold yt0 in |- *.
set (yt0_1 := cA_1 m one yt0) in |- *.
intro.
generalize (expf_L0_CNS m x' y' x_1 y H11 H12).
simpl in |- *.
fold x'_1 in |- *.
fold x'b0 in |- *.
fold y't0 in |- *.
set (y't0_1 := cA_1 m one y't0) in |- *.
intro.
generalize H13.
clear H13.
elim (expf_dec m x_1 y).
generalize H15.
clear H15.
elim (expf_dec m x'_1 y').
intros.
elim (expf_dec (L m zero x' y') x_1 y).
elim (expf_dec (L m zero x y) x'_1 y').
tauto.
intros.
clear a a0 b0 a1.
assert (betweenf m x'_1 x_1 y' /\ betweenf m x'_1 y y' \/ betweenf m y't0_1 x_1 x'b0 /\ betweenf m y't0_1 y x'b0 \/ ~ expf m x'_1 x_1 /\ expf m x_1 y).
clear H13 H14 H24 b b1 H7 H8 H17 H18.
clear H10 E0 E1 E3.
tauto.
clear H15.
clear E2.
generalize (expf_dec (L m zero x y) x'_1 y').
intro.
assert (~ (betweenf m x_1 x'_1 y /\ betweenf m x_1 y' y \/ betweenf m yt0_1 x'_1 xb0 /\ betweenf m yt0_1 y' xb0 \/ ~ expf m x_1 x'_1 /\ expf m x'_1 y')).
clear H16 H7 H8 H17 H18 b b1 E0 E1.
tauto.
clear H13 E3 H15.
elim H19.
clear H19.
elim H16.
clear H16.
intro.
assert (yt0_1 = cF m y).
unfold yt0_1 in |- *.
unfold yt0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (xb0 = cF_1 m x_1).
unfold xb0 in |- *.
unfold x_1 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
rewrite H15 in |- *.
rewrite H16 in |- *.
assert (y <> y').
intro.
symmetry in H19.
tauto.
assert (x_1 <> x'_1).
intro.
assert (cA m one x_1 = cA m one x'_1).
rewrite H21 in |- *.
tauto.
unfold x_1 in H22.
unfold x'_1 in H22.
rewrite cA_cA_1 in H22.
rewrite cA_cA_1 in H22.
symmetry in H22.
tauto.
tauto.
tauto.
tauto.
tauto.
generalize (betweenf1 m x_1 y x'_1 y' H5 H2 H21 H19).
clear H19 H21 H7 H8 H17 H18 E0 E1 H20.
tauto.
clear H16.
intros.
elim H13; clear H13; intro.
assert (yt0_1 = cF m y).
unfold yt0_1 in |- *.
unfold yt0 in |- *.
fold (cF m y) in |- *.
tauto.
assert (xb0 = cF_1 m x_1).
unfold xb0 in |- *.
unfold x_1 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
assert (y't0_1 = cF m y').
unfold y't0_1 in |- *.
unfold y't0 in |- *.
fold (cF m y') in |- *.
tauto.
assert (x'b0 = cF_1 m x'_1).
unfold x'b0 in |- *.
unfold x'_1 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
rewrite H15 in |- *.
rewrite H16 in |- *.
rewrite H19 in H13.
rewrite H21 in H13.
assert (y <> y').
intro.
symmetry in H22.
tauto.
assert (x_1 <> x'_1).
intro.
assert (cA m one x_1 = cA m one x'_1).
rewrite H23 in |- *.
tauto.
unfold x_1 in H25.
unfold x'_1 in H25.
rewrite cA_cA_1 in H25.
rewrite cA_cA_1 in H25.
symmetry in H25.
tauto.
tauto.
tauto.
tauto.
tauto.
generalize (betweenf2 m x_1 y x'_1 y' H5 H4 H23 H22).
clear H22 H23 H7 H8 H17 H18 H12 H2 E0 E1 H10.
tauto.
right.
right.
split.
intro.
assert (expf m x'_1 x_1).
apply expf_symm.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
