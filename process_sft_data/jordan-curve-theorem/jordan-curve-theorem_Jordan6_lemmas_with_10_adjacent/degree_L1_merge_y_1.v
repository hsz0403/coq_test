Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1_y_1_y0_aux:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx := MF.degree m x in let dy_1 := MF.degree m y_1 in ~expf m x y0 -> j <= dy_1 -1 -> Iter (cF m1) (dx + j) x = Iter (cF m) j y_1.
Proof.
intros.
unfold prec_L in H0.
assert (cF = MF.f).
tauto.
rewrite plus_comm in |- *.
rewrite H3 in |- *.
rewrite MF.Iter_comp in |- *.
unfold m1 in |- *.
unfold dx in |- *.
rewrite cF_L1_x10 in |- *.
fold y_1 in |- *.
induction j.
simpl in |- *.
tauto.
assert (Iter (MF.f (L m one x y)) (S j) y_1 = MF.f (L m one x y) (Iter (MF.f (L m one x y)) j y_1)).
simpl in |- *.
tauto.
rewrite H4 in |- *.
clear H4.
rewrite IHj in |- *.
rewrite <- H3 in |- *.
set (y_1j := Iter (cF m) j y_1) in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
fold y_1 in |- *.
elim (eq_dart_dec y0 y_1j).
unfold y_1j in |- *.
intro.
assert (y0 = cF_1 m y_1).
unfold y_1 in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1 in |- *.
fold y0 in |- *.
tauto.
tauto.
tauto.
rewrite a in H4.
assert (Iter (cF m) (S j) y_1 = y_1).
simpl in |- *.
rewrite H4 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
tauto.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
tauto.
generalize (MF.degree_lub m y_1 H H6).
simpl in |- *.
fold dy_1 in |- *.
intros.
decompose [and] H7.
clear H7.
generalize (H11 (S j)).
intros.
elim H7.
omega.
tauto.
intro.
elim (eq_dart_dec (cF_1 m x) y_1j).
intros.
unfold y_1j in a.
assert (y_1 = cF m y0).
unfold y0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite H4 in a.
rewrite H3 in a.
assert (x = cF m (Iter (MF.f m) j (MF.f m y0))).
rewrite <- a in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite H3 in H5.
rewrite <- MF.Iter_f_Si in H5.
elim H1.
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
split with (S (S j)).
simpl in |- *.
rewrite H5 in |- *.
simpl in |- *.
tauto.
tauto.
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
intro.
unfold y_1j in |- *.
simpl in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
omega.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
Admitted.

Lemma cF_L1_y_1_y0:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx := MF.degree m x in let dy0 := MF.degree m y0 in ~expf m x y0 -> j <= dy0 -1 -> Iter (cF m1) (dx + j) x = Iter (cF m) j y_1.
Proof.
intros.
set (dy_1 := MF.degree m y_1) in |- *.
assert (y = cA_1 m zero y0).
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (y_1 = cF m y0).
unfold y_1 in |- *.
rewrite H3 in |- *.
fold (cF m y0) in |- *.
tauto.
assert (expf m y0 y_1).
rewrite H4 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
split with 1.
simpl in |- *.
tauto.
assert (MF.degree m y0 = MF.degree m y_1).
symmetry in |- *.
apply MF.expo_degree.
tauto.
unfold expf in H5.
apply MF.expo_symm.
tauto.
tauto.
fold dy0 in H6.
fold dy_1 in H6.
unfold m1 in |- *.
unfold y_1 in |- *.
unfold dx in |- *.
apply cF_L1_y_1_y0_aux.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y_1 in |- *.
fold dy_1 in |- *.
rewrite <- H6 in |- *.
Admitted.

Lemma diff_y_1_y0_aux:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx := MF.degree m x in let dy_1 := MF.degree m y_1 in ~expf m x y0 -> j <= dy_1 -1 -> Iter (cF m1) (dx + j) x <> x.
Proof.
intros.
generalize (cF_L1_y_1_y0_aux m x y j H H0 H1).
fold y0 in |- *.
fold y_1 in |- *.
fold m1 in |- *.
fold dx in |- *.
fold dy_1 in |- *.
intros.
generalize (H3 H2).
intro.
clear H3.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m y_1 H H3).
simpl in |- *.
fold dy_1 in |- *.
intros.
decompose [and] H5.
clear H5.
rewrite H4 in |- *.
intro.
assert (y = cA_1 m zero y0).
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (y_1 = cF m y0).
unfold y_1 in |- *.
rewrite H7 in |- *.
fold (cF m y0) in |- *.
tauto.
assert (expf m y0 y_1).
rewrite H10 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
split with 1.
simpl in |- *.
tauto.
assert (expf m y_1 (Iter (cF m) j y_1)).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with j.
tauto.
elim H1.
apply expf_trans with y_1.
rewrite <- H5 in |- *.
apply expf_symm.
tauto.
apply expf_symm.
Admitted.

Lemma diff_y_1_y0:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx := MF.degree m x in let dy0 := MF.degree m y0 in ~expf m x y0 -> j <= dy0 -1 -> Iter (cF m1) (dx + j) x <> x.
Proof.
intros.
set (dy_1 := MF.degree m y_1) in |- *.
assert (y = cA_1 m zero y0).
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (y_1 = cF m y0).
unfold y_1 in |- *.
rewrite H3 in |- *.
fold (cF m y0) in |- *.
tauto.
assert (expf m y0 y_1).
rewrite H4 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
split with 1.
simpl in |- *.
tauto.
assert (MF.degree m y0 = MF.degree m y_1).
symmetry in |- *.
apply MF.expo_degree.
tauto.
unfold expf in H5.
apply MF.expo_symm.
tauto.
tauto.
fold dy0 in H6.
fold dy_1 in H6.
unfold m1 in |- *.
unfold y_1 in |- *.
unfold dx in |- *.
apply diff_y_1_y0_aux.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y_1 in |- *; fold dy_1 in |- *.
rewrite <- H6 in |- *.
Admitted.

Lemma cF_L1_y0:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let dx := MF.degree m x in let dy0 := MF.degree m y0 in ~expf m x y0 -> Iter (cF m1) (dx + dy0) x = x.
Proof.
intros.
assert (cF = MF.f).
tauto.
set (y_1 := cA_1 m one y) in |- *.
set (dy_1 := MF.degree m y_1) in |- *.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
unfold prec_L in H0.
tauto.
assert (y = cA_1 m zero y0).
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (y_1 = cF m y0).
unfold y_1 in |- *.
rewrite H4 in |- *.
fold (cF m y0) in |- *.
tauto.
assert (expf m y0 y_1).
rewrite H5 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
split with 1.
simpl in |- *.
tauto.
assert (MF.degree m y0 = MF.degree m y_1).
symmetry in |- *.
apply MF.expo_degree.
tauto.
unfold expf in H6.
apply MF.expo_symm.
tauto.
tauto.
fold dy0 in H7.
fold dy_1 in H7.
rewrite H7 in |- *.
generalize (MF.degree_lub m y_1 H H3).
simpl in |- *.
fold dy_1 in |- *.
intro.
decompose [and] H8.
clear H8.
assert (dx + dy_1 = S (dx + (dy_1 - 1))).
omega.
rewrite H8 in |- *.
simpl in |- *.
unfold dx in |- *.
unfold m1 in |- *.
rewrite cF_L1_y_1_y0 in |- *.
fold y_1 in |- *.
assert (y0 = Iter (cF m) (dy_1 - 1) y_1).
rewrite H5 in |- *.
rewrite <- H7 in |- *.
assert (cF m y0 = Iter (MF.f m) 1 y0).
simpl in |- *.
tauto.
rewrite H10 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (dy0 - 1 + 1 = dy0).
omega.
rewrite H13 in |- *.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m y0 H H14).
simpl in |- *.
fold dy0 in |- *.
intros.
symmetry in |- *.
tauto.
rewrite <- H10 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) y0).
fold y0 in |- *.
tauto.
elim (eq_dart_dec (cF_1 m x) y0).
intros.
elim H1.
rewrite <- a in |- *.
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_cF_1 m x).
unfold prec_L in H0.
tauto.
split with 1.
simpl in |- *.
tauto.
fold y0 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y_1 in |- *.
fold dy_1 in |- *.
fold y0 in |- *.
fold dy0 in |- *.
rewrite H7 in |- *.
Admitted.

Lemma ndN_L: forall(m:fmap)(k:dim)(x y:dart), ndN (L m k x y) = ndN m.
Proof.
simpl in |- *.
Admitted.

Lemma degree_L1_merge_MAX: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> ~expf m x y0 -> let MAX := MF.degree m x + MF.degree m y0 in MF.degree_aux m1 x MAX = MAX.
Proof.
intros.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
rewrite ndN_L in |- *.
set (dx := MF.degree m x) in |- *.
set (dy0 := MF.degree m y0) in |- *.
fold dx in MAX.
fold dy0 in MAX.
elim (le_lt_dec MAX (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f (L m one x y)) MAX x)).
tauto.
intro.
elim b.
unfold MAX in |- *.
unfold dx in |- *.
unfold dy0 in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H1 in |- *.
symmetry in |- *.
unfold y0 in |- *.
apply cF_L1_y0.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
fold y0 in |- *.
tauto.
intro.
unfold MAX in b.
unfold m1 in H.
simpl in H.
assert (inv_hmap m).
tauto.
unfold prec_L in H.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
unfold expf in H0.
assert (~ MF.expo m x y0).
tauto.
generalize (MF.degree_sum_bound m x y0 H1 H2 H4 H5).
fold dy0 in |- *.
fold dx in |- *.
Admitted.

Lemma degree_L1_merge_aux: forall(m:fmap)(x y:dart)(n:nat), let m1:= L m one x y in let y0 := cA m zero y in let MAX:= MF.degree m x + MF.degree m y0 in inv_hmap m1 -> ~expf m x y0 -> 1 <= MAX - n -> MF.degree_aux m1 x (MAX - n) = MF.degree m x + MF.degree m y0.
Proof.
induction n.
intros.
assert (MAX - 0 = MAX).
omega.
rewrite H2 in |- *.
unfold MAX in |- *.
unfold y0 in |- *.
unfold m1 in |- *.
apply degree_L1_merge_MAX.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
intros.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
simpl in |- *.
elim (le_lt_dec (MAX - S n) (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f (L m one x y)) (MAX - S n) x)).
intros.
fold m1 in a0.
set (i := MAX - S n) in |- *.
fold i in a0.
assert (cF = MF.f).
tauto.
rewrite <- H2 in a0.
symmetry in a0.
fold i in H1.
fold i in a.
set (dx := MF.degree m x) in |- *.
fold dx in MAX.
set (dy0 := MF.degree m y0) in |- *.
fold dy0 in MAX.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
assert (exd m x).
tauto.
assert (exd m y).
tauto.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
assert (inv_hmap m).
tauto.
generalize (MF.degree_lub m x H6 H3).
simpl in |- *.
fold dx in |- *.
rewrite <- H2 in |- *.
intros.
generalize (MF.degree_lub m y0 H6 H5).
simpl in |- *.
fold dy0 in |- *.
intros.
rewrite <- H2 in H8.
elim (le_lt_dec i (dx - 1)).
intro.
absurd (Iter (cF m1) i x = x).
unfold m1 in |- *.
apply (diff_x_x10 m x y).
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
tauto.
tauto.
intro.
elim (le_lt_dec i (dx + (dy0 - 1))).
intros.
absurd (Iter (cF m1) i x = x).
unfold m1 in |- *.
set (j := i - dx) in |- *.
assert (i = dx + j).
unfold j in |- *.
omega.
rewrite H9 in |- *.
apply (diff_y_1_y0 m x y j H6).
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
fold dy0 in |- *.
omega.
tauto.
intro.
unfold MAX in i.
unfold i in b0.
omega.
intros.
elim (eq_nat_dec (MAX - S n) (ndN m)).
intro.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
decompose [and] H; clear H.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
assert (~ MF.expo m x y0).
unfold expf in H0.
tauto.
generalize (MF.degree_sum_bound m x y0 H2 H4 H H7).
intro.
unfold MAX in a.
unfold MAX in a0.
generalize (MF.ndN_pos m x H4).
intro.
omega.
intro.
assert (MAX - S n + 1 = MAX - n).
omega.
rewrite H2 in |- *.
unfold MAX in |- *.
apply IHn.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
fold MAX in |- *.
omega.
intro.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
decompose [and] H; clear H.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
assert (~ MF.expo m x y0).
unfold expf in H0.
tauto.
generalize (MF.degree_sum_bound m x y0 H2 H4 H H7).
intro.
unfold MAX in b.
Admitted.

Theorem degree_L1_merge_x: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> ~expf m x y0 -> MF.degree m1 x = MF.degree m x + MF.degree m y0.
Proof.
intros.
set (dx := MF.degree m x) in |- *.
set (dy0 := MF.degree m y0) in |- *.
fold y0 in |- *.
set (MAX := dx + dy0) in |- *.
generalize (degree_L1_merge_aux m x y (MAX - 1) H H0).
fold y0 in |- *.
fold m1 in |- *.
fold dx in |- *.
fold dy0 in |- *.
fold MAX in |- *.
intros.
simpl in H.
unfold prec_L in H.
decompose [and] H.
clear H.
generalize (MF.degree_lub m x H2 H4).
simpl in |- *.
fold dx in |- *.
intros.
assert (0 < MAX).
unfold MAX in |- *.
omega.
assert (MAX - (MAX - 1) = 1).
omega.
rewrite H9 in H1.
unfold MF.degree in |- *.
apply H1.
Admitted.

Theorem orb_x_eqs_orb_y0: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> eqs (MF.Iter_orb m1 x) (MF.Iter_orb m1 y0).
Proof.
intros.
apply MF.eqs_orb.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H1 in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 y0).
tauto.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H.
Admitted.

Lemma expf_L1_x_y0: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> ~expf m x y0 -> expf m1 x y0.
Proof.
intros.
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
unfold m1 in |- *.
simpl in |- *.
generalize (exd_cA m zero y).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H1 in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) y0).
tauto.
fold y0 in |- *.
tauto.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
Admitted.

Theorem degree_L1_merge_y0: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> ~expf m x y0 -> MF.degree m1 y0 = MF.degree m x + MF.degree m y0.
Proof.
intros.
assert (expf m1 y0 x).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
unfold m1 in |- *.
simpl in |- *.
generalize (exd_cA m zero y).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H1 in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) y0).
tauto.
fold y0 in |- *.
tauto.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
rewrite (MF.expo_degree m1 y0 x H) in |- *.
unfold y0 in |- *.
unfold m1 in |- *.
apply degree_L1_merge_x.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
unfold expf in H1.
Admitted.

Lemma not_expf_L1_x: forall(m:fmap)(x y z:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> ~expf m1 x z.
Proof.
intros.
intro.
assert (MF.expo1 m1 x z).
unfold expf in H3.
generalize (MF.expo_expo1 m1 x z).
tauto.
unfold MF.expo1 in H4.
decompose [and] H4.
clear H4.
elim H6.
intros i Hi.
unfold m1 in Hi.
rewrite MF.upb_eq_degree in Hi.
rewrite degree_L1_merge_x in Hi.
set (dx := MF.degree m x) in |- *.
fold y0 in Hi.
set (dy0 := MF.degree m y0) in Hi.
fold dx in Hi.
decompose [and] Hi.
clear Hi H6.
elim H1.
unfold expf in |- *.
split.
unfold m1 in H.
simpl in H.
tauto.
assert (inv_hmap m1).
tauto.
unfold m1 in H6.
simpl in H6.
unfold prec_L in H6.
decompose [and] H6.
clear H6.
assert (cF = MF.f).
tauto.
elim (le_lt_dec i (dx - 1)).
intro.
unfold MF.expo in |- *.
split.
tauto.
rewrite <- H6 in |- *.
split with i.
rewrite <- (cF_L1_x_x10 m x y i) in |- *.
rewrite H6 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
intro.
elim (le_lt_dec i (dx + (dy0 - 1))).
intro.
elim H2.
unfold expf in |- *.
split.
tauto.
set (y_1 := cA_1 m one y) in |- *.
assert (MF.expo m y0 y_1).
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
split with 1.
simpl in |- *.
rewrite <- H6 in |- *.
unfold y0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
apply MF.expo_trans with y_1.
tauto.
unfold MF.expo in |- *.
split.
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
tauto.
split with (i - dx).
rewrite <- H6 in |- *.
unfold y_1 in |- *.
rewrite <- (cF_L1_y_1_y0 m x y (i - dx)) in |- *.
fold dx in |- *.
assert (dx + (i - dx) = i).
omega.
rewrite H15 in |- *.
fold m1 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
fold dy0 in |- *.
omega.
intro.
absurd (dx + (dy0 - 1) < i).
omega.
tauto.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold m1 in |- *.
tauto.
simpl in |- *.
Admitted.

Lemma not_expf_L1_y0: forall(m:fmap)(x y z:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> ~expf m1 y0 z.
Proof.
intros.
intro.
assert (expf m1 x y0).
unfold m1 in |- *.
unfold y0 in |- *.
apply (expf_L1_x_y0 m x y H).
fold y0 in |- *.
tauto.
generalize (not_expf_L1_x m x y z H H0 H1 H2).
fold m1 in |- *.
intro.
elim H5.
apply expf_trans with y0.
tauto.
Admitted.

Lemma Iter_cF_L1_i: forall(m:fmap)(x y z:dart)(i:nat), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> exd m z -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> Iter (cF m1) i z = Iter (cF m) i z.
Proof.
intros.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
set (zi := Iter (cF m) i z) in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
set (y_1 := cA_1 m one y) in |- *.
assert (inv_hmap m1).
tauto.
unfold m1 in H4.
simpl in H4.
unfold prec_L in H4.
decompose [and] H4.
assert (expf m z zi).
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
unfold zi in |- *.
tauto.
elim (eq_dart_dec y0 zi).
intro.
rewrite <- a in H10.
elim H3.
apply expf_symm.
tauto.
elim (eq_dart_dec (cF_1 m x) zi).
intros.
rewrite <- a in H10.
elim H2.
apply expf_trans with (cF_1 m x).
apply expf_symm.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
generalize (exd_cF_1 m x).
tauto.
split with 1.
simpl in |- *.
assert (MF.f = cF).
tauto.
rewrite H12 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
apply expf_symm.
tauto.
tauto.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
Admitted.

Theorem expf_L1_eq:forall(m:fmap)(x y z t:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> (expf m1 z t <-> expf m z t).
Proof.
intros.
split.
unfold m1 in |- *.
unfold expf in |- *.
simpl in |- *.
unfold prec_L in |- *.
intros.
decompose [and] H3.
clear H3.
unfold MF.expo in H5.
decompose [and] H5.
clear H5.
simpl in H3.
elim H10.
intros i Hi.
clear H10.
assert (MF.f = cF).
tauto.
unfold MF.expo in |- *.
split.
tauto.
split.
tauto.
split with i.
rewrite H5 in |- *.
rewrite H5 in Hi.
rewrite <- (Iter_cF_L1_i m x y z i) in |- *.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
unfold expf in |- *.
simpl in |- *.
intros.
split.
unfold m1 in H.
simpl in H.
tauto.
unfold MF.expo in H3.
decompose [and] H3.
clear H3.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
elim H7.
intros i Hi.
split with i.
assert (MF.f = cF).
tauto.
rewrite H3 in |- *.
rewrite H3 in Hi.
unfold m1 in |- *.
rewrite (Iter_cF_L1_i m x y z i) in |- *.
tauto.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
Admitted.

Lemma expf_impl_expf_L1:forall(m:fmap)(x y z t:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 t -> expf m z t -> expf m1 z t.
Proof.
intros.
assert (~ expf m y0 z).
intro.
elim H2.
apply expf_trans with z.
tauto.
tauto.
generalize (expf_L1_eq m x y z t H H0 H1 H4).
Admitted.

Theorem orb_L1_eqs: forall(m:fmap)(x y z:dart), let m1:= L m one x y in let y0:= cA m zero y in inv_hmap m1 -> exd m z -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> eqs (MF.Iter_orb m1 z) (MF.Iter_orb m z).
Proof.
intros.
unfold eqs in |- *.
intro t.
generalize (expf_L1_eq m x y z t H H1 H2 H3).
fold m1 in |- *.
intro.
generalize (MF.expo_eq_exds_orb m z t).
intros.
generalize (MF.expo_eq_exds_orb m1 z t).
intros.
assert (inv_hmap m1).
tauto.
unfold m1 in H7.
simpl in H7.
unfold prec_L in H7.
decompose [and] H7.
clear H7.
assert (exd m z <-> exd m1 z).
unfold m1 in |- *.
simpl in |- *.
tauto.
split.
intro.
assert (exd m1 z).
unfold m1 in |- *.
simpl in |- *.
tauto.
generalize (MF.incls_orbit m1 z H H15).
intros.
assert (fmap_to_set m1 = fmap_to_set m).
unfold m1 in |- *.
simpl in |- *.
tauto.
rewrite H17 in H16.
inversion H16.
generalize (H18 t H13).
intro.
generalize (exd_exds m t).
intro.
clear H18.
assert (exd m t).
tauto.
assert (exd m1 t).
unfold m1 in |- *.
simpl in |- *.
tauto.
unfold expf in H4.
tauto.
intro.
assert (exd m1 z).
unfold m1 in |- *.
simpl in |- *.
tauto.
generalize (MF.incls_orbit m1 z H H15).
intros.
assert (fmap_to_set m1 = fmap_to_set m).
unfold m1 in |- *.
simpl in |- *.
tauto.
generalize (MF.incls_orbit m z H8 H0).
intros.
inversion H18.
generalize (H19 t H13).
intro.
unfold expf in H4.
generalize (exd_exds m t).
intro.
clear H19.
assert (exd m1 t).
unfold m1 in |- *.
simpl in |- *.
tauto.
assert (exd m t).
tauto.
Admitted.

Lemma degree_L1_merge_x_others_aux: forall(m:fmap)(x y z:dart)(n:nat), let m1:= L m one x y in let y0 := cA m zero y in let dz:= MF.degree m z in inv_hmap m1 -> exd m z -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> n < dz -> MF.degree_aux m1 z (dz - n) = MF.degree_aux m z (dz - n).
Proof.
induction n.
intros.
rename H4 into dzp.
assert (dz - 0 = dz).
omega.
rewrite H4 in |- *.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
rewrite ndN_L in |- *.
fold m1 in |- *.
rewrite (MF.degree_aux_equation m z dz) in |- *.
elim (le_lt_dec dz (ndN m)).
elim (eq_dart_dec z (Iter (MF.f m1) dz z)).
intros.
unfold m1 in a.
elim (eq_dart_dec z (Iter (MF.f m) dz z)).
tauto.
intro.
assert (MF.f = cF).
tauto.
rewrite H5 in a.
rewrite H5 in b.
rewrite Iter_cF_L1_i in a.
tauto.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
intro.
generalize (MF.degree_lub m z).
simpl in |- *.
fold dz in |- *.
intro.
elim b.
symmetry in |- *.
unfold m1 in H.
simpl in H.
unfold m1 in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H6 in |- *.
rewrite <- H6 in H5.
rewrite Iter_cF_L1_i in |- *.
tauto.
simpl in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
intros.
rename H4 into dzp.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
rewrite ndN_L in |- *.
rewrite (MF.degree_aux_equation m z (dz - S n)) in |- *.
elim (le_lt_dec (dz - S n) (ndN m)).
assert (MF.f = cF).
tauto.
rewrite H4 in |- *.
rewrite Iter_cF_L1_i in |- *.
elim (eq_dart_dec z (Iter (cF m) (dz - S n) z)).
tauto.
intros.
elim (eq_nat_dec (dz - S n) (ndN m)).
tauto.
intros.
assert (dz - S n + 1 = dz - n).
assert (dz <> S n).
intro.
rewrite H5 in b.
simpl in b.
assert (n - n = 0).
omega.
rewrite H6 in b.
simpl in b.
tauto.
generalize (MF.degree_lub m z).
simpl in |- *.
fold dz in |- *.
unfold m1 in H.
intro.
assert (0 < dz).
simpl in H.
tauto.
omega.
rewrite H5 in |- *.
unfold dz in |- *.
apply IHn.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold dz in |- *.
omega.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
Admitted.

Theorem degree_L1_merge_x_others: forall(m:fmap)(x y z:dart), let m1:= L m one x y in let y0 := cA m zero y in inv_hmap m1 -> exd m z -> ~expf m x y0 -> ~expf m x z -> ~expf m y0 z -> MF.degree m1 z = MF.degree m z.
Proof.
intros.
unfold MF.degree in |- *.
unfold m1 in |- *.
generalize (MF.degree_lub m z).
simpl in |- *.
set (dz := MF.degree m z) in |- *.
intro.
assert (0 < dz).
unfold m1 in H.
simpl in H.
tauto.
assert (1 = dz - (dz - 1)).
omega.
rewrite H6 in |- *.
unfold dz in |- *.
apply degree_L1_merge_x_others_aux.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold dz in |- *.
Admitted.

Theorem degree_L1_merge_y_1: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y_1 := cA_1 m one y in inv_hmap m1 -> ~expf m x y_1 -> MF.degree m1 x = MF.degree m x + MF.degree m y_1.
Proof.
intros.
set (y0 := cA m zero y) in |- *.
assert (~ expf m x y0).
intro.
unfold m1 in H.
simpl in H.
decompose [and] H.
clear H.
generalize (expf_y0_y_1 m x y H2 H3).
simpl in |- *.
fold y0 in |- *.
fold y_1 in |- *.
intro.
elim H0.
apply expf_trans with y0.
tauto.
tauto.
unfold y_1 in |- *.
rewrite <- (degree_y0_y_1 m x y) in |- *.
unfold m1 in |- *.
apply degree_L1_merge_x.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
unfold m1 in |- *.
unfold m1 in H.
simpl in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
