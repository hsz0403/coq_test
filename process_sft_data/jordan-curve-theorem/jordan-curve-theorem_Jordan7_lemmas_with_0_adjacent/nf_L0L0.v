Require Export Jordan6.

Theorem nf_L0L0:forall (m:fmap)(x y x' y':dart), let m1:= L (L m zero x y) zero x' y' in let m2:= L (L m zero x' y') zero x y in inv_hmap m1 -> nf m1 = nf m2.
Proof.
intros.
unfold m1 in H.
unfold m1 in |- *.
unfold m2 in |- *.
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
elim (expf_dec m (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
omega.
intros.
generalize (nf_L0L0_I m x y x' y' H a1 a0 a b).
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
elim (expf_dec m (cA_1 m one x') y').
tauto.
tauto.
tauto.
elim (expf_dec m (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
tauto.
elim (expf_dec m (cA_1 m one x') y').
tauto.
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L0.
tauto.
unfold m2 in H0.
generalize (nf_L0L0_I m x' y' x y H0 a0 a1 a b).
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
elim (expf_dec m (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
rewrite H1 in |- *.
tauto.
tauto.
tauto.
tauto.
intros.
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
intros.
generalize (nf_L0L0_II m x y x' y' H a1 b a a0).
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
elim (expf_dec m (cA_1 m one x') y').
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
tauto.
tauto.
tauto.
tauto.
intros.
generalize (nf_L0L0_IV m x y x' y' H a0 b0 b a).
simpl in |- *.
elim (expf_dec m (cA_1 m one x') y').
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
elim (expf_dec m (cA_1 m one x) y).
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
tauto.
tauto.
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
intros.
omega.
intros.
generalize (nf_L0L0_VI m x y x' y' H a b1 b b0).
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
elim (expf_dec m (cA_1 m one x') y').
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
tauto.
tauto.
tauto.
elim (expf_dec m (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L0.
tauto.
unfold m2 in H0.
generalize (nf_L0L0_II m x' y' x y H0 a1 b a a0).
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
tauto.
elim (expf_dec m (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
symmetry in |- *.
tauto.
tauto.
tauto.
tauto.
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L0.
tauto.
generalize (nf_L0L0_IV m x' y' x y H0 a0 b0 b a).
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
elim (expf_dec m (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
tauto.
tauto.
elim (expf_dec m (cA_1 m one x') y').
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
intros.
symmetry in |- *.
tauto.
tauto.
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
omega.
intros.
assert (inv_hmap m2).
unfold m2 in |- *; apply inv_hmap_L0L0.
tauto.
generalize (nf_L0L0_VI m x' y' x y H0 a b1 b b0).
simpl in |- *.
elim (expf_dec m (cA_1 m one x') y').
elim (expf_dec m (cA_1 m one x) y).
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
tauto.
intros.
symmetry in |- *.
tauto.
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
omega.
intros.
generalize (nf_L0L0_V m x y x' y' H b1 b0 a b).
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
tauto.
elim (expf_dec m (cA_1 m one x') y').
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
assert (inv_hmap m2).
unfold m2 in |- *.
apply inv_hmap_L0L0.
tauto.
generalize (nf_L0L0_V m x' y' x y H0 b0 b1 a b).
simpl in |- *.
elim (expf_dec m (cA_1 m one x) y).
tauto.
elim (expf_dec m (cA_1 m one x') y').
tauto.
elim (expf_dec (L m zero x' y') (cA_1 m one x) y).
tauto.
elim (expf_dec (L m zero x y) (cA_1 m one x') y').
intros.
symmetry in |- *.
tauto.
tauto.
intros.
omega.
