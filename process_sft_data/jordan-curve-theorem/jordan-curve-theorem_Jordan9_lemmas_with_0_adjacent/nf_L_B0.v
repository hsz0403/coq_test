Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Lemma nf_L_B0:forall (m:fmap)(x:dart), inv_hmap m -> succ m zero x -> nf (L (B m zero x) zero x (A m zero x)) = nf m.
Proof.
intros.
induction m.
simpl in |- *.
unfold succ in H0.
simpl in H0.
tauto.
rename t into u.
simpl in |- *.
simpl in H.
unfold prec_I in H.
unfold succ in H0.
simpl in H0.
assert (exd m x).
apply (succ_exd m zero x).
tauto.
unfold succ in |- *.
tauto.
elim (eq_dart_dec d x).
intro.
rewrite a in H.
tauto.
intro.
assert (exd (B m zero x) x).
generalize (exd_B m zero x x).
tauto.
assert (inv_hmap (B m zero x)).
generalize (inv_hmap_B m zero x).
tauto.
assert (prec_I (B m zero x) d).
unfold prec_I in |- *.
split.
tauto.
intro.
generalize (exd_B m zero x d).
tauto.
assert (exd (B m zero x) (cA_1 (B m zero x) one x)).
generalize (exd_B m zero x (cA_1 (B m zero x) one x)).
generalize (exd_cA_1 (B m zero x) one x).
tauto.
assert (d <> cA_1 (B m zero x) one x).
rewrite cA_1_B_ter.
intro.
rewrite H6 in H.
absurd (exd m (cA_1 m one x)).
tauto.
generalize (exd_cA_1 m one x).
tauto.
tauto.
intro.
inversion H6.
assert (nf (L (B m zero x) zero x (A m zero x)) = nf m).
apply IHm.
tauto.
unfold succ in |- *.
tauto.
simpl in H7.
generalize (expf_I (B m zero x) d (cA_1 (B m zero x) one x) (A m zero x) u p H3 H4 H5 H6).
intro.
generalize H7.
clear H7.
elim (expf_dec (I (B m zero x) d u p) (cA_1 (B m zero x) one x) (A m zero x)).
intro.
elim (expf_dec (B m zero x) (cA_1 (B m zero x) one x) (A m zero x)).
intros.
clear H8 a a0.
omega.
intro.
absurd (expf (B m zero x) (cA_1 (B m zero x) one x) (A m zero x)).
tauto.
tauto.
elim (expf_dec (B m zero x) (cA_1 (B m zero x) one x) (A m zero x)).
intros.
absurd (expf (I (B m zero x) d u p) (cA_1 (B m zero x) one x) (A m zero x)).
tauto.
tauto.
intros.
clear H8 b0 b1.
omega.
unfold succ in H0.
assert (inv_hmap (L m d d0 d1)).
tauto.
simpl in H.
unfold prec_L in H.
decompose [and] H.
clear H.
induction d.
elim (eq_dart_dec d0 x).
intro.
assert (B (L m zero d0 d1) zero x = m).
simpl in |- *.
elim (eq_dart_dec d0 x).
tauto.
tauto.
rewrite H.
rewrite <- a.
assert (A (L m zero d0 d1) zero d0 = d1).
simpl in |- *.
elim (eq_dart_dec d0 d0).
tauto.
tauto.
rewrite H7.
tauto.
intro.
rewrite B_L.
assert (A (L m zero d0 d1) zero x = A m zero x).
simpl in |- *.
elim (eq_dart_dec d0 x).
tauto.
tauto.
rewrite H.
rewrite nf_L0L0.
assert (nf (L m zero d0 d1) = nf m + (if expf_dec m (cA_1 m one d0) d1 then 1 else -1)).
simpl in |- *.
tauto.
set (m' := L (B m zero x) zero x (A m zero x)) in |- *.
unfold nf at 1 in |- *.
fold nf in |- *.
rewrite H7.
unfold m' in |- *.
rewrite IHm.
fold m' in |- *.
assert (cA_1 m' one d0 = cA_1 m one d0).
unfold m' in |- *.
simpl in |- *.
rewrite cA_1_B_ter.
tauto.
tauto.
intro.
inversion H9.
rewrite H9.
assert (expf m' (cA_1 m one d0) d1 <-> expf m (cA_1 m one d0) d1).
unfold m' in |- *.
generalize (expf_L_B m zero x (cA_1 m one d0) d1 H2).
intro.
apply H10.
unfold succ in |- *.
rewrite <- H.
tauto.
elim (expf_dec m' (cA_1 m one d0) d1).
elim (expf_dec m (cA_1 m one d0) d1).
intros.
trivial.
tauto.
elim (expf_dec m (cA_1 m one d0) d1).
tauto.
intros.
clear H10 b0 b1.
omega.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
simpl in |- *.
split.
split.
apply inv_hmap_B.
tauto.
assert (prec_L (B m zero x) zero d0 d1).
unfold prec_L in |- *.
split.
generalize (exd_B m zero x d0).
tauto.
split.
generalize (exd_B m zero x d1).
tauto.
split.
unfold succ in |- *.
rewrite A_B_bis.
unfold succ in H5.
tauto.
tauto.
split.
unfold pred in |- *.
elim (eq_nat_dec d1 (A m zero x)).
intro.
rewrite a.
rewrite A_1_B.
tauto.
tauto.
intro.
rewrite A_1_B_bis.
unfold pred in H6.
tauto.
tauto.
tauto.
rewrite cA_B.
elim (eq_dart_dec x d0).
intro.
symmetry in a.
tauto.
intro.
elim (eq_dart_dec (top m zero x) d0).
intro.
intro.
rewrite <- H7 in H6.
unfold pred in H6.
rewrite A_1_A in H6.
absurd (x <> nil).
tauto.
intro.
rewrite H9 in H7.
simpl in H7.
rewrite A_nil in H7.
absurd (exd m d1).
rewrite <- H7.
apply not_exd_nil.
tauto.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
tauto.
unfold prec_L in |- *.
split.
simpl in |- *.
generalize (exd_B m zero x x).
assert (exd m x).
apply succ_exd with zero.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
tauto.
simpl in |- *.
split.
generalize (exd_B m zero x (A m zero x)).
assert (exd m (A m zero x)).
apply succ_exd_A.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
tauto.
split.
unfold succ in |- *.
simpl in |- *.
elim (eq_dart_dec d0 x).
tauto.
intro.
rewrite A_B.
tauto.
tauto.
split.
unfold pred in |- *.
simpl in |- *.
elim (eq_dart_dec d1 (A m zero x)).
intro.
rewrite a in H6.
unfold pred in H6.
rewrite A_1_A in H6.
elim H6.
assert (exd m x).
apply succ_exd with zero.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
apply exd_not_nil with m.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
intro.
rewrite A_1_B.
tauto.
tauto.
elim (eq_dart_dec d0 x).
tauto.
elim (eq_dart_dec (cA_1 (B m zero x) zero d1) x).
intros.
rewrite cA_B.
elim (eq_dart_dec x d0).
intro.
symmetry in a0.
tauto.
elim (eq_dart_dec (top m zero x) d0).
intros.
generalize a.
clear a.
rewrite cA_1_B.
elim (eq_dart_dec (A m zero x) d1).
intros.
rewrite a1 in a0.
tauto.
elim (eq_dart_dec (bottom m zero x) d1).
intros.
rewrite <- a0 in H8.
rewrite cA_top in H8.
tauto.
tauto.
apply succ_exd with zero.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
intros.
rewrite cA_1_eq in a.
generalize a.
elim (pred_dec m zero d1).
tauto.
intros.
rewrite <- a1 in a0.
rewrite top_top in a0.
rewrite a1 in a0.
tauto.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
intros.
intro.
assert (cA m zero x = A m zero x).
assert (succ m zero x).
unfold succ in |- *.
rewrite <- H.
tauto.
rewrite cA_eq.
elim (succ_dec m zero x).
tauto.
tauto.
tauto.
rewrite <- H9 in H7.
elim b2.
rewrite <- (cA_1_cA m zero x).
rewrite <- H7.
rewrite cA_1_cA.
tauto.
tauto.
tauto.
tauto.
apply succ_exd with zero.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
intros.
rewrite cA_B.
elim (eq_dart_dec x x).
intros.
intro.
apply (not_pred_bottom m zero x H2).
rewrite H7.
unfold pred in |- *.
rewrite A_1_A.
apply (exd_not_nil m x).
tauto.
apply succ_exd with zero.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
tauto.
tauto.
unfold succ in |- *.
rewrite <- H.
tauto.
tauto.
assert (A (L m one d0 d1) zero x = A m zero x).
simpl in |- *.
tauto.
rewrite H.
assert (succ m zero x).
unfold succ in |- *.
rewrite <- H.
tauto.
assert (exd m x).
apply succ_exd with zero.
tauto.
tauto.
rewrite B_L_ter.
assert (inv_hmap (B m zero x)).
apply inv_hmap_B.
tauto.
assert (inv_hmap (L (B m zero x) zero x (A m zero x))).
simpl in |- *.
split.
tauto.
unfold prec_L in |- *.
unfold succ in |- *.
unfold pred in |- *.
assert (exd (B m zero x) x).
generalize (exd_B m zero x x).
tauto.
assert (exd (B m zero x) (A m zero x)).
generalize (exd_B m zero x (A m zero x)).
assert (exd m (A m zero x)).
apply succ_exd_A.
tauto.
tauto.
tauto.
assert (~ A_1 (B m zero x) zero (A m zero x) <> nil).
rewrite A_1_B.
tauto.
tauto.
assert (~ A (B m zero x) zero x <> nil).
rewrite A_B.
tauto.
tauto.
assert (cA (B m zero x) zero x <> A m zero x).
rewrite cA_B.
elim (eq_dart_dec x x).
intro.
apply succ_bottom.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
assert (inv_hmap (L (L (B m zero x) zero x (A m zero x)) one d0 d1)).
simpl in |- *.
split.
split.
tauto.
simpl in H11.
tauto.
unfold prec_L in |- *.
simpl in |- *.
assert (exd (B m zero x) d0).
generalize (exd_B m zero x d0).
tauto.
assert (exd (B m zero x) d1).
generalize (exd_B m zero x d1).
tauto.
assert (~ succ (B m zero x) one d0).
unfold succ in |- *.
rewrite A_B_ter.
unfold succ in H5.
tauto.
intro.
inversion H14.
assert (~ pred (B m zero x) one d1).
unfold pred in |- *.
rewrite A_1_B_ter.
unfold pred in H6.
tauto.
intro.
inversion H15.
assert (cA (B m zero x) one d0 <> d1).
rewrite cA_B_ter.
tauto.
tauto.
intro.
inversion H16.
tauto.
rewrite <- nf_L0L1.
set (m' := L (B m zero x) zero x (A m zero x)) in |- *.
unfold nf in |- *.
fold nf in |- *.
assert (nf m' = nf m).
unfold m' in |- *.
apply IHm.
tauto.
tauto.
rewrite H13.
assert (cA m' zero d1 = cA m zero d1).
unfold m' in |- *.
rewrite cA_L_B.
tauto.
tauto.
tauto.
rewrite H14.
generalize (expf_L_B m zero x d0 (cA m zero d1) H2 H7).
intro.
elim (expf_dec m' d0 (cA m zero d1)).
elim (expf_dec m d0 (cA m zero d1)).
intros.
clear H15 a a0.
omega.
tauto.
elim (expf_dec m d0 (cA m zero d1)).
tauto.
intros.
clear H15 b b0.
omega.
tauto.
intro.
inversion H10.
