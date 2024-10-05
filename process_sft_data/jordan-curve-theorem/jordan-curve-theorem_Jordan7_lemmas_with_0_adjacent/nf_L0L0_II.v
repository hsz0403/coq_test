Require Export Jordan6.

Lemma nf_L0L0_II:forall (m:fmap)(x y x' y':dart), let m1:= L (L m zero x y) zero x' y' in let m2:= L (L m zero x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let x'_1 := cA_1 m one x' in expf m x_1 y -> ~ expf m x'_1 y' -> expf (L m zero x' y') x_1 y -> expf (L m zero x y) x'_1 y' -> nf m1 = nf m2.
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
tauto.
elim (expf_dec (L m zero x' y') x_1 y).
elim (expf_dec (L m zero x y) x'_1 y').
intros.
clear a a0 b0 a1.
assert (betweenf m x_1 x'_1 y /\ betweenf m x_1 y' y \/ betweenf m yt0_1 x'_1 xb0 /\ betweenf m yt0_1 y' xb0 \/ ~ expf m x_1 x'_1 /\ expf m x'_1 y').
clear H15 H7 H8 H17 H18.
tauto.
clear H13.
clear H15.
elim E1.
clear E1.
elim H16; clear H16; intro.
decompose [and] H13.
clear H13.
generalize (betweenf_expf m x_1 x'_1 y H5 H12 H15).
intro.
generalize (betweenf_expf m x_1 y' y H5 H12 H16).
intro.
apply expf_trans with x_1.
apply expf_symm.
tauto.
tauto.
elim H13.
clear H13.
intros.
decompose [and] H13.
clear H13.
assert (exd m yt0_1).
unfold yt0_1 in |- *.
generalize (exd_cA_1 m one yt0).
assert (exd m yt0).
unfold yt0 in |- *.
generalize (exd_cA_1 m zero y).
tauto.
tauto.
generalize (betweenf_expf m yt0_1 x'_1 xb0 H5 H13 H15).
generalize (betweenf_expf m yt0_1 y' xb0 H5 H13 H16).
intros.
apply expf_trans with yt0_1.
apply expf_symm.
tauto.
tauto.
clear H13.
tauto.
tauto.
tauto.
tauto.
