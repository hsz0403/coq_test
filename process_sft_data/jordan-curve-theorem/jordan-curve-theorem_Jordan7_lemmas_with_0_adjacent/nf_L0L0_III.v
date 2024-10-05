Require Export Jordan6.

Lemma nf_L0L0_III:forall (m:fmap)(x y x' y':dart), let m1:= L (L m zero x y) zero x' y' in let m2:= L (L m zero x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let x'_1 := cA_1 m one x' in expf m x_1 y -> ~ expf m x'_1 y' -> expf (L m zero x' y') x_1 y -> ~ expf (L m zero x y) x'_1 y' -> nf m1 = nf m2.
Proof.
intros.
unfold m1 in |- *.
unfold m2 in |- *.
simpl in |- *.
fold x_1 in |- *.
fold x'_1 in |- *.
elim (expf_dec m x_1 y).
elim (expf_dec m x'_1 y').
tauto.
elim (expf_dec (L m zero x' y') x_1 y).
elim (expf_dec (L m zero x y) x'_1 y').
tauto.
intros.
omega.
tauto.
tauto.
