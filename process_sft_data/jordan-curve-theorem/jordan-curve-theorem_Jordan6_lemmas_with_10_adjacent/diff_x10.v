Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1:forall(m:fmap)(x y z:dart), inv_hmap m -> prec_L m one x y -> let x10 := cF_1 m x in let y0 := cA m zero y in let y_1 := cA_1 m one y in let m1:= L m one x y in cF m1 z = if eq_dart_dec y0 z then x else if eq_dart_dec x10 z then y_1 else cF m z.
Proof.
intros.
elim (exd_dec m z).
intro.
rename a into Ez.
generalize (cF_L m one x y z).
elim (eq_dim_dec one zero).
intro.
inversion a.
intros.
generalize (H1 H H0).
clear H1.
elim (eq_dart_dec y (cA_1 m zero z)).
intro.
elim (eq_dart_dec y0 z).
fold m1 in |- *.
tauto.
intros.
elim b0.
unfold y0 in |- *.
rewrite a in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA m one x) (cA_1 m zero z)).
fold m1 in |- *.
intros.
elim (eq_dart_dec y0 z).
unfold y0 in |- *.
intro.
elim b0.
rewrite <- a0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
elim (eq_dart_dec x10 z).
intros.
unfold y_1 in |- *.
tauto.
intros.
unfold x10 in b1.
elim b1.
unfold cF_1 in |- *.
rewrite a in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec y0 z).
intro.
unfold y0 in a.
elim b1.
rewrite <- a in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
elim (eq_dart_dec x10 z).
unfold x10 in |- *.
intros.
unfold cF_1 in a.
elim b0.
rewrite <- a in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
generalize (exd_cA m one x).
unfold prec_L in H0.
tauto.
fold m1 in H1.
fold (cF m z) in H1.
tauto.
intros.
elim (eq_dart_dec y0 z).
intro.
unfold y0 in a.
elim b.
rewrite <- a in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
elim (eq_dart_dec x10 z).
unfold x10 in |- *.
intros.
elim b.
rewrite <- a in |- *.
generalize (exd_cF_1 m x).
unfold prec_L in H0.
tauto.
generalize (exd_cF_not_nil m z H).
intro.
assert (inv_hmap m1).
unfold m1 in |- *.
simpl in |- *.
tauto.
assert (~ exd m1 z).
unfold m1 in |- *.
simpl in |- *.
tauto.
generalize (exd_cF_not_nil m1 z H2).
intro.
intros.
generalize (exd_dec m z).
intro.
generalize (exd_dec m1 z).
intro.
generalize (eq_dart_dec (cF m z) nil).
generalize (eq_dart_dec (cF m1 z) nil).
intros.
assert (cF m z = nil).
tauto.
assert (cF m1 z = nil).
tauto.
rewrite H9 in |- *.
Admitted.

Lemma expf_y0_y_1:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in expf m y0 y_1.
Proof.
intros.
assert (exd m y).
unfold prec_L in H0.
tauto.
assert (exd m y0).
unfold y0 in |- *.
generalize (exd_cA m zero y).
tauto.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with 1.
simpl in |- *.
unfold y0 in |- *.
unfold y_1 in |- *.
assert (MF.f = cF).
tauto.
rewrite H3 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
Admitted.

Lemma degree_y0_y_1:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in MF.degree m y0 = MF.degree m y_1.
Proof.
intros.
apply MF.expo_degree.
tauto.
generalize (expf_y0_y_1 m x y H H0).
simpl in |- *.
fold y0 in |- *.
fold y_1 in |- *.
unfold expf in |- *.
Admitted.

Lemma cF_L1_x_x10:forall(m:fmap)(x y:dart)(i:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let dx := MF.degree m x in let m1:= L m one x y in ~expf m x y0 -> i <= dx - 1 -> Iter (cF m1) i x = Iter (cF m) i x.
Proof.
intros.
unfold prec_L in H0.
assert (exd m x).
tauto.
generalize (MF.degree_lub m x H H3).
simpl in |- *.
fold dx in |- *.
intros.
decompose [and] H4.
clear H4.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H4 in H8.
rewrite <- H4 in H7.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
set (x10 := cF_1 m x) in |- *.
set (y_1 := cA_1 m one y) in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 (Iter (cF m) i x)).
intro.
elim H1.
rewrite a in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
tauto.
rewrite <- H4 in |- *.
split with i.
tauto.
elim (eq_dart_dec x10 (Iter (cF m) i x)).
intros.
assert (i = dx - 1).
apply (MF.unicity_mod_p m x i (dx - 1) H H3).
assert (MF.Iter_upb m x = dx).
unfold dx in |- *.
apply MF.upb_eq_degree.
tauto.
tauto.
rewrite H6 in |- *.
omega.
rewrite MF.upb_eq_degree in |- *.
fold dx in |- *.
omega.
tauto.
tauto.
rewrite <- H4 in |- *.
rewrite <- a in |- *.
unfold x10 in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite H6 in |- *.
rewrite H4 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite <- H4 in |- *.
rewrite H7 in |- *.
tauto.
tauto.
tauto.
omega.
absurd (i = dx - 1).
omega.
tauto.
intros.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
Admitted.

Lemma diff_x_x10:forall(m:fmap)(x y:dart)(i:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let dx := MF.degree m x in let m1:= L m one x y in ~expf m x y0 -> 0 < i <= dx - 1 -> Iter (cF m1) i x <> x.
Proof.
intros.
generalize (cF_L1_x_x10 m x y i H H0).
simpl in |- *.
fold y0 in |- *; fold dx in |- *.
fold m1 in |- *.
intros.
generalize (H3 H1).
clear H3.
intro.
rewrite H3 in |- *.
unfold prec_L in H0.
assert (exd m x).
tauto.
generalize (MF.degree_lub m x H H4).
simpl in |- *.
fold dx in |- *.
intros.
decompose [and] H5.
clear H5.
apply H9.
split.
omega.
omega.
Admitted.

Lemma cF_L1_x10:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx := MF.degree m x in ~expf m x y0 -> Iter (cF m1) dx x = y_1.
Proof.
intros.
unfold prec_L in H0.
assert (exd m x).
tauto.
generalize (MF.degree_lub m x H H2).
simpl in |- *.
fold dx in |- *.
intros.
decompose [and] H3.
clear H3.
set (x10 := cF_1 m x) in |- *.
assert (x10 = Iter (cF m) (dx - 1) x).
unfold x10 in |- *.
assert (MF.Iter_upb m x = dx).
unfold dx in |- *.
apply MF.upb_eq_degree.
tauto.
tauto.
assert (cF_1 = MF.f_1).
tauto.
assert (cF = MF.f).
tauto.
rewrite H5 in |- *.
rewrite H8 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite H6 in |- *.
tauto.
tauto.
tauto.
omega.
assert (dx = S (dx - 1)).
omega.
rewrite H5 in |- *.
simpl in |- *.
unfold m1 in |- *.
rewrite cF_L1_x_x10 in |- *.
rewrite <- H3 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
fold x10 in |- *.
fold y_1 in |- *.
elim (eq_dart_dec y0 x10).
unfold x10 in |- *.
intro.
elim H1.
rewrite a in |- *.
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
assert (cF = MF.f).
tauto.
rewrite <- H8 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec x10 x10).
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
Admitted.

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

Lemma diff_x10:forall(m:fmap)(x y:dart), inv_hmap m -> prec_L m one x y -> let m1:= L m one x y in let y0 := cA m zero y in let dx := MF.degree m x in ~expf m x y0 -> Iter (cF m1) dx x <> x.
Proof.
intros.
unfold dx in |- *.
unfold m1 in |- *.
rewrite cF_L1_x10 in |- *.
intro.
apply H1.
unfold expf in |- *.
split.
tauto.
apply MF.expo_symm.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
assert (cA_1 m one y = cF m y0).
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
rewrite <- H2 in |- *.
rewrite H3 in |- *.
split with 1.
simpl in |- *.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
