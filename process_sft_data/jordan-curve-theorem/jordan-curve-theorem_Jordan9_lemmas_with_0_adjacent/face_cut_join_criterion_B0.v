Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Theorem face_cut_join_criterion_B0:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> let y := A m zero x in let x0 := bottom m zero x in (expf m y x0 <-> ~expf (B m zero x) y x0).
Proof.
intros.
generalize (expf_not_expf_B0 m x H H0).
intros.
simpl in H1.
assert (cA m zero x = A m zero x).
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
rewrite H2 in H1.
fold y in H1.
fold x0 in H1.
assert (expf (B m zero x) y x0 <-> expf (B m zero x) (cA_1 m one x) y).
unfold x0 in |- *.
unfold expf in |- *.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
assert (cA (B m zero x) zero x = bottom m zero x).
rewrite cA_B.
elim (eq_dart_dec x x).
tauto.
tauto.
tauto.
tauto.
assert (cA_1 m one x = cA_1 (B m zero x) one x).
rewrite cA_1_B_ter.
tauto.
tauto.
intro.
inversion H5.
rewrite <- H4.
rewrite H5.
assert (MF.expo (B m zero x) y (cA (B m zero x) zero x) <-> MF.expo (B m zero x) (cA_1 (B m zero x) one x) y).
assert (MF.expo (B m zero x) (cA (B m zero x) zero x) (cA_1 (B m zero x) one x)).
unfold MF.expo in |- *.
split.
generalize (exd_cA (B m zero x) zero x).
assert (exd (B m zero x) x).
generalize (exd_B m zero x x).
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
tauto.
tauto.
split with 1%nat.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H6.
unfold cF in |- *.
rewrite cA_1_cA.
tauto.
tauto.
generalize (exd_B m zero x x).
generalize (succ_exd m zero x).
tauto.
split.
intro.
assert (MF.expo (B m zero x) (cA (B m zero x) zero x) y).
apply MF.expo_symm.
tauto.
tauto.
apply MF.expo_trans with (cA (B m zero x) zero x).
apply MF.expo_symm.
tauto.
tauto.
tauto.
intro.
apply MF.expo_symm.
tauto.
apply MF.expo_trans with (cA_1 (B m zero x) one x).
tauto; tauto.
tauto.
tauto.
generalize (expf_dec (B m zero x) y x0).
generalize (expf_dec m y x0).
tauto.
