Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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

Lemma expf_L1_x: forall (m:fmap)(x y z:dart), let y0 := cA m zero y in let m1 := L m one x y in inv_hmap m1 -> ~expf m x y0 -> expf m x z -> expf m1 x z.
Proof.
intros.
unfold expf in |- *.
split.
tauto.
unfold expf in H1.
decompose [and] H1.
clear H1.
generalize (MF.expo_expo1 m x z).
intros.
assert (MF.expo1 m x z).
tauto.
unfold MF.expo1 in H4.
set (dx := MF.Iter_upb m x) in |- *.
fold dx in H4.
assert (exists j : nat, j < dx /\ Iter (MF.f m) j x = z).
tauto.
elim H5.
intros i Hi.
decompose [and] Hi.
assert (MF.f = cF).
tauto.
rewrite H8 in H7.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
split with i.
rewrite H8 in |- *.
unfold m1 in |- *.
rewrite <- H7 in |- *.
apply cF_L1_x_x10.
tauto.
unfold m1 in H.
simpl in H.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold dx in |- *.
omega.
tauto.
Admitted.

Lemma expf_L1_y0: forall (m:fmap)(x y z:dart), let y0 := cA m zero y in let m1 := L m one x y in inv_hmap m1 -> ~expf m x y0 -> expf m y0 z -> expf m1 y0 z.
Proof.
intros.
set (y_1 := cA_1 m one y) in |- *.
assert (expf m y_1 z).
apply expf_trans with y0.
apply expf_symm.
unfold expf in |- *.
split.
unfold m1 in H; simpl in H.
tauto.
unfold MF.expo in |- *.
split.
unfold y0 in |- *.
generalize (exd_cA m zero y).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
split with 1.
simpl in |- *.
unfold y_1 in |- *.
unfold y0 in |- *.
unfold MF.f in |- *.
unfold McF.f in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
unfold m1 in H; simpl in H.
tauto.
unfold m1 in H; simpl in H; unfold prec_L in H.
tauto.
tauto.
apply expf_trans with x.
apply expf_symm.
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_x_y0.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
unfold expf in |- *.
unfold expf in H2.
assert (MF.expo1 m y_1 z).
generalize (MF.expo_expo1 m y_1 z).
intro.
assert (MF.expo1 m y_1 z).
tauto.
tauto.
unfold MF.expo1 in H3.
decompose [and] H3.
clear H3.
elim H5.
clear H5.
intros j Hj.
set (dy_1 := MF.Iter_upb m y_1) in |- *.
fold dy_1 in Hj.
decompose [and] Hj.
clear Hj.
split.
unfold m1 in |- *.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
unfold m1 in H.
simpl in H.
unfold prec_L in H.
tauto.
set (dx := MF.degree m x) in |- *.
unfold y_1 in dy_1.
split with (dx + j).
assert (MF.f = cF).
tauto.
rewrite H6 in |- *.
unfold m1 in |- *.
unfold dx in |- *.
rewrite cF_L1_y_1_y0_aux in |- *.
fold y_1 in |- *.
rewrite <- H6 in |- *.
tauto.
unfold m1 in H.
tauto.
unfold m1 in H.
simpl in H.
tauto.
fold y0 in |- *.
tauto.
rewrite <- MF.upb_eq_degree in |- *.
fold dy_1 in |- *.
omega.
unfold m1 in |- *.
tauto.
generalize (exd_cA_1 m one y).
unfold m1 in H.
simpl in H.
unfold prec_L in H.
Admitted.

Theorem degree_L1_merge_summary: forall (m:fmap)(x y z:dart), let y0 := cA m zero y in let m1 := L m one x y in inv_hmap m1 -> exd m z -> ~expf m x y0 -> let dx:= MF.degree m x in let dy0:= MF.degree m y0 in MF.degree m1 z = if expf_dec m x z then dx + dy0 else if expf_dec m y0 z then dx + dy0 else MF.degree m z.
Proof.
intros.
elim (expf_dec m x z).
intro.
assert (expf m1 x z).
unfold m1 in |- *.
apply expf_L1_x.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
tauto.
rewrite (MF.expo_degree m1 z x) in |- *.
unfold dx in |- *.
unfold dy0 in |- *.
unfold m1 in |- *.
unfold y0 in |- *.
apply degree_L1_merge_x.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
tauto.
unfold expf in H2.
apply MF.expo_symm.
tauto.
tauto.
elim (expf_dec m y0 z).
intros.
assert (expf m1 y0 z).
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_y0.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite (MF.expo_degree m1 z y0) in |- *.
unfold dx in |- *.
unfold dy0 in |- *.
unfold m1 in |- *.
unfold y0 in |- *.
apply degree_L1_merge_y0.
fold m1 in |- *.
tauto.
fold y0 in |- *.
tauto.
tauto.
apply MF.expo_symm.
tauto.
unfold expf in H2.
tauto.
intros.
unfold m1 in |- *.
apply degree_L1_merge_x_others.
fold m1 in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
Admitted.

Lemma or_and_dec : forall (A B C D:Prop), dec A -> dec B -> dec C -> dec D -> {A /\ B \/ C /\ D} + {~A /\ ~C \/ ~B /\ ~C \/ ~A /\ ~D \/ ~B /\ ~D}.
Proof.
unfold dec in |- *.
intros.
Admitted.

Lemma expf_L1_I_CS:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in ~ expf m x y0 -> ( expf m z t \/ expf m z x /\ expf m t y0 \/ expf m t x /\ expf m z y0 ) -> expf (L m one x y) z t.
Proof.
intros.
generalize (expf_dec m z x).
intro AA.
generalize (expf_dec m t y0).
intro BB.
generalize (expf_dec m t x).
intro CC.
generalize (expf_dec m z y0).
intro DD.
generalize (or_and_dec (expf m z x) (expf m t y0) (expf m t x) (expf m z y0)).
unfold dec in |- *.
intros.
generalize (H3 AA BB CC DD).
clear H3.
intro.
elim H3.
clear H3.
intro.
elim a.
clear a.
intro.
set (m1 := L m one x y) in |- *.
assert (expf m1 z x).
unfold m1 in |- *.
apply expf_symm.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
assert (expf m1 t y0).
apply expf_symm.
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_y0.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
apply expf_symm.
tauto.
apply expf_trans with y0.
apply expf_trans with x.
tauto.
unfold y0 in |- *.
unfold m1 in |- *.
apply expf_L1_x_y0.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
clear a.
intro.
set (m1 := L m one x y) in |- *.
clear H2.
assert (expf m1 t x).
unfold m1 in |- *.
apply expf_symm.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
assert (expf m1 z y0).
apply expf_symm.
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_y0.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
apply expf_symm.
tauto.
apply expf_trans with y0.
tauto.
apply expf_trans with x.
apply expf_symm.
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_x_y0.
tauto.
fold y0 in |- *.
tauto.
unfold m1 in |- *.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
intros.
clear H3.
assert (expf m z t).
tauto.
clear H2.
set (m1 := L m one x y) in |- *.
assert (expf m1 x y0).
unfold m1 in |- *; unfold y0 in |- *.
apply expf_L1_x_y0.
tauto.
fold y0 in |- *.
tauto.
elim b.
clear b.
intro.
decompose [and] H4.
clear H4.
elim BB.
intro.
assert (expf m y0 z).
apply expf_trans with t.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
assert (expf m1 y0 z).
unfold m1 in |- *.
unfold y0 in |- *.
apply expf_L1_y0.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
assert (expf m1 t y0).
apply expf_symm.
unfold y0 in |- *.
unfold m1 in |- *.
apply expf_L1_y0.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
apply expf_symm.
tauto.
apply expf_symm.
apply expf_trans with y0.
tauto.
tauto.
intro.
unfold m1 in |- *.
apply expf_symm.
apply expf_impl_expf_L1.
tauto.
fold y0 in |- *.
tauto.
intro.
elim H6.
apply expf_symm.
tauto.
fold y0 in |- *.
intro.
elim b.
apply expf_trans with z.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
clear b.
intro.
elim H4.
clear H4.
intro.
decompose [and] H4.
clear H4.
assert (~ expf m y0 t).
intro.
elim H5.
apply expf_symm.
tauto.
assert (~ expf m x t).
intro.
elim H6.
apply expf_symm.
tauto.
unfold m1 in |- *.
generalize (expf_L1_eq m x y t z H H1 H7 H4).
intro.
apply expf_symm.
assert (expf m t z).
apply expf_symm.
tauto.
tauto.
clear H4.
intro.
elim H4.
clear H4.
intro.
elim H4.
clear H4.
intros.
assert (~ expf m x z).
intro.
elim H4.
apply expf_symm.
tauto.
assert (~ expf m y0 z).
intro.
elim H5.
apply expf_symm.
tauto.
unfold m1 in |- *.
generalize (expf_L1_eq m x y z t H H1 H6 H7).
tauto.
clear H4.
intro.
elim H4.
clear H4.
intros.
elim AA.
intro.
assert (expf m t x).
apply expf_trans with z.
apply expf_symm.
tauto.
tauto.
assert (expf m1 z x).
unfold m1 in |- *.
apply expf_symm.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
assert (expf m1 t x).
apply expf_symm.
unfold m1 in |- *.
apply expf_L1_x.
tauto.
fold y0 in |- *.
tauto.
apply expf_symm.
tauto.
apply expf_trans with x.
tauto.
apply expf_symm.
tauto.
intro.
unfold m1 in |- *.
assert (~ expf m x z).
intro.
elim b.
apply expf_symm.
tauto.
assert (~ expf m y0 z).
intro.
elim H5.
apply expf_symm.
tauto.
generalize (expf_L1_eq m x y z t H H1 H6 H7).
Admitted.

Lemma expf_L1_I_CN:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in ~ expf m x y0 -> expf (L m one x y) z t -> ( expf m z t \/ expf m z x /\ expf m t y0 \/ expf m t x /\ expf m z y0 ).
Proof.
intros.
elim (expf_dec m z t).
tauto.
intro.
right.
elim (expf_dec m z x).
intro.
elim (expf_dec m t y0).
tauto.
intro.
right.
assert (~ expf m x t).
intro.
elim b.
apply expf_trans with x.
tauto.
tauto.
assert (~ expf m y0 t).
intro.
elim b0.
apply expf_symm.
tauto.
assert (expf (L m one x y) t z).
apply expf_symm.
tauto.
assert (~ expf m t z).
intro.
elim b.
apply expf_symm.
tauto.
generalize (expf_L1_eq m x y t z H H1 H3 H4).
tauto.
intro.
elim (expf_dec m t y0).
intro.
assert (~ expf m y0 z).
intro.
elim b.
apply expf_trans with y0.
apply expf_symm.
tauto.
apply expf_symm.
tauto.
assert (~ expf m x z).
intro.
elim b0.
apply expf_symm.
tauto.
generalize (expf_L1_eq m x y z t H H1 H4 H3).
tauto.
intro.
right.
elim (expf_dec m t x).
intro.
elim (expf_dec m z y0).
tauto.
intro.
assert (~ expf m x z).
intro.
elim b0.
apply expf_symm.
tauto.
assert (~ expf m y0 z).
intro.
elim b2.
apply expf_symm.
tauto.
generalize (expf_L1_eq m x y z t H H1 H3 H4).
tauto.
intro.
assert (~ expf m x t).
intro.
elim b2.
apply expf_symm.
tauto.
assert (~ expf m y0 t).
intro.
elim b1.
apply expf_symm.
tauto.
assert (~ expf m t z).
intro.
elim b.
apply expf_symm.
tauto.
assert (expf (L m one x y) t z).
apply expf_symm.
tauto.
generalize (expf_L1_eq m x y t z H H1 H3 H4).
Admitted.

Lemma cF_L1_x_y0:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> (i <= j < dx - 1) -> Iter (cF m1) i x = Iter (cF m) i x.
Proof.
intros.
induction i.
simpl in |- *.
tauto.
simpl in |- *.
rewrite IHi in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
assert (cF = MF.f).
tauto.
rewrite H4 in |- *.
assert (cF_1 = MF.f_1).
tauto.
rewrite H5 in |- *.
elim (eq_dart_dec y0 (Iter (MF.f m) i x)).
intro.
rewrite H4 in H1.
rewrite H1 in a.
assert (j = i).
apply (MF.degree_unicity m x j i).
tauto.
unfold prec_L in H0.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
omega.
tauto.
absurd (j = i).
omega.
tauto.
elim (eq_dart_dec (MF.f_1 m x) (Iter (MF.f m) i x)).
intros.
assert (x = MF.f m (Iter (MF.f m) i x)).
rewrite <- a in |- *.
rewrite <- H4 in |- *.
rewrite <- H5 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (x = Iter (MF.f m) (S i) x).
simpl in |- *.
tauto.
assert (exd m x).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m x H H8).
simpl in |- *.
fold dx in |- *.
intros.
decompose [and] H9.
symmetry in H7.
absurd (Iter (MF.f m) (S i) x = x).
apply H13.
omega.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma diff_cF_L1_x_y0:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> (0 < i <= j /\ j < dx - 1) -> Iter (cF m1) i x <> x.
Proof.
intros.
unfold m1 in |- *.
rewrite (cF_L1_x_y0 m x y i j H H0) in |- *.
assert (exd m x).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m x H H4).
simpl in |- *.
fold dx in |- *.
intro.
decompose [and] H5.
clear H5.
apply H9.
omega.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
Admitted.

Lemma cF_L1_y0_x:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in j < dx - 1 -> y0 = Iter (cF m) j x -> expf m x y0 -> Iter (cF m1) (j + 1) x = x.
Proof.
intros.
assert (S j = j + 1).
omega.
rewrite <- H4 in |- *.
simpl in |- *.
unfold m1 in |- *.
rewrite (cF_L1_x_y0 m x y j j) in |- *.
rewrite <- H2 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 y0).
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
Admitted.

Lemma cF_L1_y_1_x10:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> j < dx - 1 -> j + 1 + i <= dx - 1 -> Iter (cF m1) i y_1 = Iter (cF m) (j + 1 + i) x.
intros.
intros.
induction i.
simpl in |- *.
assert (j + 1 + 0 = S j).
omega.
rewrite H5 in |- *.
simpl in |- *.
rewrite <- H1 in |- *.
unfold y0 in |- *.
unfold y_1 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
assert (j + 1 + S i = S (j + 1 + i)).
omega.
rewrite H5 in |- *.
simpl in |- *.
clear H5.
rewrite IHi in |- *.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 (Iter (cF m) (j + 1 + i) x)).
intros.
rewrite H1 in a.
assert (j = j + 1 + i).
assert (exd m x).
unfold prec_L in H0.
tauto.
apply (MF.degree_unicity m x).
tauto.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
omega.
tauto.
absurd (j = j + 1 + i).
omega.
tauto.
elim (eq_dart_dec (cF_1 m x) (Iter (cF m) (j + 1 + i) x)).
intros.
assert (x = Iter (cF m) (S (j + 1 + i)) x).
simpl in |- *.
rewrite <- a in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
symmetry in H5.
absurd (Iter (cF m) (S (j + 1 + i)) x = x).
apply MF.degree_diff.
tauto.
unfold prec_L in H0.
tauto.
fold dx in |- *.
omega.
tauto.
tauto.
tauto.
tauto.
Admitted.

Lemma diff_cF_L1_y_1_x10:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> j + 1 + i <= dx - 1 -> Iter (cF m1) i y_1 <> x.
Proof.
intros.
unfold m1 in |- *.
unfold y_1 in |- *.
rewrite (cF_L1_y_1_x10 m x y i j H H0) in |- *.
assert (exd m x).
unfold prec_L in H0.
tauto.
generalize (MF.degree_lub m x H H4).
simpl in |- *.
fold dx in |- *.
intro.
decompose [and] H5.
clear H5.
apply H9.
omega.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
Admitted.

Lemma diff_cF_L1_y_1_y_1:forall(m:fmap)(x y:dart)(i j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> j + 1 + i <= dx - 1 -> 0 < i -> Iter (cF m1) i y_1 <> y_1.
Proof.
intros.
unfold m1 in |- *.
unfold y_1 in |- *.
rewrite (cF_L1_y_1_x10 m x y i j) in |- *.
fold y_1 in |- *.
assert (y_1 = Iter (cF m) 1 y0).
simpl in |- *.
unfold y0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
rewrite H5 in |- *.
rewrite H1 in |- *.
rewrite <- MF.Iter_comp in |- *.
intro.
assert (j + 1 + i = 1 + j).
apply (MF.degree_unicity m x).
tauto.
unfold prec_L in H0.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
omega.
tauto.
absurd (j + 1 + i = 1 + j).
omega.
tauto.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
fold dx in |- *.
omega.
fold dx in |- *.
Admitted.

Lemma cF_L1_x10_y_1:forall(m:fmap)(x y:dart)(j:nat), inv_hmap m -> prec_L m one x y -> let y0 := cA m zero y in let y_1:= cA_1 m one y in let x1:= cA m one x in let x10:= cA m zero x1 in let dx := MF.degree m x in let m1:= L m one x y in y0 = Iter (cF m) j x -> expf m x y0 -> j < dx - 1 -> Iter (cF m1) (dx - (j + 1)) y_1 = y_1.
Proof.
intros.
assert (dx - (j + 1) = S (dx - (j + 2))).
omega.
rewrite H4 in |- *.
clear H4.
simpl in |- *.
unfold m1 in |- *.
unfold y_1 in |- *.
rewrite (cF_L1_y_1_x10 m x y (dx - (j + 2)) j) in |- *.
assert (j + 1 + (dx - (j + 2)) = dx - 1).
omega.
rewrite H4 in |- *.
clear H4.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold dx in |- *.
rewrite MF.degree_per in |- *.
assert (MF.f_1 = cF_1).
tauto.
assert (exd m (cF_1 m x)).
generalize (exd_cF_1 m x).
unfold prec_L in H0.
tauto.
rewrite H4 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) (cF_1 m x)).
intro.
assert (y = cA_1 m zero (cF_1 m x)).
rewrite <- a in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
unfold cF_1 in H6.
rewrite cA_1_cA in H6.
symmetry in H6.
unfold prec_L in H0.
tauto.
tauto.
generalize (exd_cA m one x).
unfold prec_L in H0.
tauto.
intro.
elim (eq_dart_dec (cF_1 m x) (cF_1 m x)).
fold y_1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
unfold prec_L in H0.
tauto.
tauto.
unfold prec_L in H0.
tauto.
omega.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
fold dx in |- *.
Admitted.

Lemma degree_L1_split_x_aux: forall(m:fmap)(x y:dart)(j i:nat), let m1:= L m one x y in let y0 := cA m zero y in let dx:= MF.degree m x in y0 = Iter (cF m) j x -> i < j < dx - 1 -> expf m x y0 -> inv_hmap m1 -> MF.degree_aux m1 x (j - i) = j + 1.
Proof.
intros.
assert (inv_hmap m1).
tauto.
unfold m1 in H2.
simpl in H2.
unfold prec_L in H2.
decompose [and] H2.
clear H2.
generalize (MF.degree_bound m x H4 H6).
fold dx in |- *.
intro.
assert (cF = MF.f).
tauto.
intros.
induction i.
assert (j - 0 = j).
omega.
rewrite H11 in |- *.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
simpl in |- *.
fold m1 in |- *.
clear H11.
elim (le_lt_dec j (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f m1) j x)).
intro.
symmetry in a0.
absurd (Iter (MF.f m1) j x = x).
unfold m1 in |- *.
rewrite <- H9 in |- *.
rewrite (cF_L1_x_y0 m x y j j) in |- *.
apply (MF.degree_diff m x H4 H6).
fold dx in |- *.
omega.
tauto.
unfold prec_L in |- *.
tauto.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
tauto.
elim (eq_nat_dec j (ndN m)).
intros.
omega.
intros.
unfold m1 in |- *.
rewrite MF.degree_aux_equation in |- *.
simpl in |- *.
fold m1 in |- *.
elim (le_lt_dec (j + 1) (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f m1) (j + 1) x)).
tauto.
intro.
elim b1.
assert (S j = j + 1).
omega.
rewrite <- H11 in |- *.
simpl in |- *.
unfold m1 in |- *.
rewrite <- H9 in |- *.
rewrite (cF_L1_x_y0 m x y j j) in |- *.
rewrite <- H in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 y0).
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
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
intro.
omega.
intro.
omega.
unfold m1 in |- *.
rewrite MF.degree_aux_equation in |- *.
simpl in |- *.
fold m1 in |- *.
elim (le_lt_dec (j - S i) (ndN m)).
intro.
elim (eq_dart_dec x (Iter (MF.f m1) (j - S i) x)).
intro.
symmetry in a0.
absurd (Iter (MF.f m1) (j - S i) x = x).
unfold m1 in |- *.
rewrite <- H9 in |- *.
apply (diff_cF_L1_x_y0 m x y (j - S i) j).
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
split.
omega.
omega.
tauto.
intro.
elim (eq_nat_dec (j - S i) (ndN m)).
intro.
omega.
intro.
assert (j - S i + 1 = j - i).
omega.
rewrite H11 in |- *.
apply IHi.
omega.
intros.
Admitted.

Theorem degree_L1_split_x_y0: forall(m:fmap)(x y:dart)(j:nat), let m1:= L m one x y in let y0 := cA m zero y in let dx:= MF.degree m x in y0 = Iter (cF m) j x -> inv_hmap m1 -> j < dx -1 -> expf m x y0 -> MF.degree m1 x = j + 1.
Proof.
intros.
assert (inv_hmap m1).
tauto.
intros.
assert (inv_hmap m1).
tauto.
unfold m1 in H3.
simpl in H3.
unfold prec_L in H3.
decompose [and] H3.
clear H3.
generalize (MF.degree_bound m x H5 H7).
generalize (MF.degree_pos m x H7).
fold dx in |- *.
intros.
unfold MF.degree in |- *.
elim (eq_nat_dec j 0).
intro.
rewrite a in |- *.
simpl in H.
simpl in |- *.
rewrite MF.degree_aux_equation in |- *.
elim (le_lt_dec 1 (ndN m1)).
intro.
unfold m1 in a0.
simpl in a0.
elim (eq_dart_dec x (Iter (MF.f m1) 1 x)).
tauto.
intro.
elim b.
simpl in |- *.
unfold m1 in |- *.
assert (cF = MF.f).
tauto.
rewrite <- H12 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 x).
tauto.
rewrite a in H.
simpl in H.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
unfold m1 in |- *.
simpl in |- *.
intro.
omega.
intro.
unfold MF.degree in |- *.
assert (1 = j - (j - 1)).
omega.
rewrite H12 in |- *.
unfold m1 in |- *.
rewrite degree_L1_split_x_aux in |- *.
omega.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
fold y0 in |- *.
tauto.
fold m1 in |- *.
Admitted.

Theorem degree_L1_split_x_y_1: forall(m:fmap)(x y:dart)(j:nat), let m1:= L m one x y in let y0 := cA m zero y in let y_1 := cA_1 m one y in let dx:= MF.degree m x in y_1 = Iter (cF m) j x -> inv_hmap m1 -> 1 <= j <= dx -1 -> expf m x y0 -> MF.degree m1 x = j.
Proof.
intros.
assert (j = S (j - 1)).
omega.
assert (y0 = Iter (cF m) (j - 1) x).
rewrite H3 in H.
simpl in H.
assert (Iter (cF m) (j - 1) x = cF_1 m y_1).
rewrite H in |- *.
rewrite cF_1_cF in |- *.
tauto.
unfold m1 in H0.
simpl in H0.
tauto.
generalize (MF.exd_Iter_f m (j - 1) x).
unfold m1 in H0.
simpl in H0.
unfold prec_L in H0.
tauto.
unfold y_1 in H4.
unfold cF_1 in H4.
rewrite cA_cA_1 in H4.
fold y0 in H4.
symmetry in |- *.
tauto.
unfold m1 in H0.
simpl in H0.
unfold prec_L in H0.
tauto.
unfold m1 in H0.
simpl in H0.
unfold prec_L in H0.
tauto.
unfold m1 in |- *.
rewrite (degree_L1_split_x_y0 m x y (j - 1)) in |- *.
omega.
fold y0 in |- *.
tauto.
fold m1 in |- *.
tauto.
fold dx in |- *.
omega.
fold y0 in |- *.
Admitted.

Lemma degree_L1_split_y_1_aux: forall(m:fmap)(x y:dart)(j i:nat), let m1:= L m one x y in let y0 := cA m zero y in let y_1:= cA_1 m one y in let dx:= MF.degree m x in y0 = Iter (cF m) j x -> j + 1 + i < dx -> expf m x y0 -> inv_hmap m1 -> MF.degree_aux m1 y_1 (dx - (j + 1 + i)) = dx - (j + 1).
Proof.
intros.
assert (inv_hmap m1).
tauto.
unfold m1 in H2.
simpl in H2.
unfold prec_L in H2.
decompose [and] H2.
clear H2.
generalize (MF.degree_bound m x H4 H6).
fold dx in |- *.
intro.
assert (cF = MF.f).
tauto.
induction i.
assert (j + 1 + 0 = j + 1).
omega.
rewrite H11 in |- *.
clear H11.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
simpl in |- *.
fold m1 in |- *.
elim (le_lt_dec (dx - (j + 1)) (ndN m)).
intro.
elim (eq_dart_dec y_1 (Iter (MF.f m1) (dx - (j + 1)) y_1)).
tauto.
intro.
elim b.
symmetry in |- *.
rewrite <- H9 in |- *.
assert (dx - (j + 1) = S (dx - j - 2)).
omega.
rewrite H11 in |- *.
simpl in |- *.
unfold y_1 in |- *.
unfold m1 in |- *.
rewrite (cF_L1_y_1_x10 m x y (dx - j - 2) j) in |- *.
assert (j + 1 + (dx - j - 2) = dx - 1).
clear H11.
omega.
rewrite H12 in |- *.
rewrite H9 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold dx in |- *.
rewrite MF.degree_per in |- *.
rewrite <- H9 in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H13 in |- *.
rewrite cF_L1 in |- *.
elim (eq_dart_dec (cA m zero y) (cF_1 m x)).
intro.
unfold cF_1 in a0.
assert (y = cA_1 m zero (cA m zero (cA m one x))).
rewrite <- a0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
rewrite cA_1_cA in H14.
rewrite H14 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
tauto.
generalize (exd_cA m one x).
tauto.
elim (eq_dart_dec (cF_1 m x) (cF_1 m x)).
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H12.
clear H11.
omega.
clear H11.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
clear H11.
omega.
fold dx in |- *.
clear H11.
omega.
intro.
omega.
rewrite MF.degree_aux_equation in |- *.
unfold m1 in |- *.
simpl in |- *.
fold m1 in |- *.
elim (le_lt_dec (dx - (j + 1 + S i)) (ndN m)).
intro.
elim (eq_dart_dec y_1 (Iter (MF.f m1) (dx - (j + 1 + S i)) y_1)).
intro.
symmetry in a0.
absurd (Iter (MF.f m1) (dx - (j + 1 + S i)) y_1 = y_1).
unfold m1 in |- *.
unfold y_1 in |- *.
apply (diff_cF_L1_y_1_y_1 m x y (dx - (j + 1 + S i)) j).
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
omega.
tauto.
elim (eq_nat_dec (dx - (j + 1 + S i)) (ndN m)).
intro.
intro.
omega.
intros.
assert (dx - (j + 1 + S i) + 1 = dx - (j + 1 + i)).
omega.
rewrite H11 in |- *.
apply IHi.
clear H11.
omega.
intro.
Admitted.

Lemma degree_L1_split_y_1: forall(m:fmap)(x y:dart)(j:nat), let m1:= L m one x y in let y0 := cA m zero y in let y_1:= cA_1 m one y in let dx:= MF.degree m x in y0 = Iter (cF m) j x -> j < dx - 1 -> expf m x y0 -> inv_hmap m1 -> MF.degree m1 y_1 = dx - (j + 1).
Proof.
intros.
unfold MF.degree in |- *.
unfold m1 in |- *.
unfold y_1 in |- *.
unfold dx in |- *.
set (i := dx - 2 - j) in |- *.
assert (1 = dx - (j + 1 + i)).
unfold i in |- *.
omega.
rewrite H3 in |- *.
unfold dx in |- *.
rewrite degree_L1_split_y_1_aux in |- *.
fold dx in |- *.
rewrite <- H3 in |- *.
tauto.
fold y0 in |- *.
tauto.
fold dx in |- *.
omega.
fold y0 in |- *.
tauto.
unfold m1 in H2.
Admitted.

Lemma expf_not_orbit_x_aux: forall (m:fmap)(x y z:dart)(i:nat), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in let t:= Iter (cF m) i z in expf m x y0 -> ~ expf m x z -> expf (L m one x y) z t.
Proof.
induction i.
simpl in |- *.
intros.
apply expf_refl.
simpl in |- *.
tauto.
simpl in |- *.
tauto.
intros.
unfold t in |- *.
set (zi := Iter (cF m) i z) in |- *.
apply expf_trans with zi.
unfold zi in |- *.
apply IHi.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
simpl in |- *.
fold zi in |- *.
set (m1 := L m one x y) in |- *.
assert (cF m1 zi = cF m zi).
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
elim (eq_dart_dec y0 zi).
fold y0 in |- *.
intro.
unfold zi in a.
assert (expf m z y0).
unfold expf in |- *.
split.
simpl in H.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with i.
assert (MF.f = cF).
tauto.
rewrite H3 in |- *.
rewrite <- a in |- *.
tauto.
elim H2.
apply expf_trans with y0.
tauto.
apply expf_symm.
tauto.
elim (eq_dart_dec (cF_1 m x) zi).
intro.
intros.
assert (x = cF m zi).
rewrite <- a in |- *.
rewrite cF_cF_1 in |- *.
tauto.
simpl in H; tauto.
simpl in H; unfold prec_L in H; tauto.
elim H2.
apply expf_symm.
rewrite H3 in |- *.
unfold zi in |- *.
unfold expf in |- *.
split.
simpl in H; unfold prec_L in H; tauto.
unfold MF.expo in |- *.
split.
tauto.
split with (S i).
simpl in |- *.
tauto.
tauto.
simpl in H; unfold prec_L in H; tauto.
simpl in H; tauto.
rewrite <- H3 in |- *.
unfold expf in |- *.
split.
unfold m1 in |- *.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
unfold zi in |- *.
generalize (MF.exd_Iter_f m i z).
simpl in H.
tauto.
split with 1.
simpl in |- *.
Admitted.

Lemma expf_not_orbit_x: forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in expf m x y0 -> ~ expf m x z -> expf m z t -> expf (L m one x y) z t.
Proof.
intros.
unfold expf in H3.
unfold MF.expo in H3.
decompose [and] H3.
clear H3.
elim H7.
intros i Hi.
clear H7.
rewrite <- Hi in |- *.
Admitted.

Lemma and_not : forall (A B : Prop), dec A -> dec B -> {A /\ ~ B } + {~ A \/ B}.
Proof.
unfold dec in |- *.
intros.
Admitted.

Lemma expf_L1_II_CS:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in expf m x y0 -> ( betweenf m x z y0 /\ betweenf m x t y0 \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10 \/ ~ expf m x z /\ expf m z t ) -> expf (L m one x y) z t.
Proof.
intros.
generalize (expf_dec m x z).
generalize (expf_dec m z t).
intros AA BB.
fold (dec (expf m z t)) in AA.
fold (dec (expf m x z)) in BB.
elim (and_not (expf m z t) (expf m x z) AA BB).
intro.
apply expf_not_orbit_x.
tauto.
tauto.
fold y0 in |- *.
tauto.
tauto.
tauto.
intro.
elim H2.
intro.
decompose [and] H3.
clear H3.
unfold betweenf in H4.
unfold MF.between in H4.
simpl in H; unfold prec_L in H.
elim H4.
clear H4.
intros iz Hiz.
elim Hiz.
intros iy01 Hi.
decompose [and] Hi.
clear Hi Hiz.
clear H2.
unfold betweenf in H5.
unfold MF.between in H5.
elim H5.
clear H5.
intros it Hi.
elim Hi.
intros iy02 Hj.
decompose [and] Hj.
clear Hi Hj.
assert (iy01 = iy02).
apply (MF.unicity_mod_p m x).
simpl in H; tauto.
simpl in H; unfold prec_L in H; tauto.
tauto.
tauto.
rewrite H7 in |- *.
tauto.
assert (MF.f = cF).
tauto.
rewrite H11 in H3.
rewrite H11 in H2.
assert (Iter (MF.f m) iy01 x = y0).
tauto.
rename H12 into E1.
assert (Iter (MF.f m) iy02 x = y0).
tauto.
rename H12 into E2.
assert (iy01 <> MF.Iter_upb m x - 1).
intro.
rewrite H12 in H6.
generalize H6.
rewrite <- MF.Iter_f_f_1 in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
intro.
assert (y = cA_1 m zero (MF.f_1 m x)).
rewrite H13 in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
assert (MF.f_1 m x = cF_1 m x).
tauto.
rewrite H15 in H14.
unfold cF_1 in H14.
rewrite cA_1_cA in H14.
symmetry in H14.
tauto.
tauto.
generalize (exd_cA m one x).
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
rewrite <- (cF_L1_x_y0 m x y iz iy01) in H3.
rewrite <- (cF_L1_x_y0 m x y it iy02) in H2.
assert (expf (L m one x y) x z).
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *; tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
tauto.
split with iz.
rewrite H11 in |- *.
rewrite H3 in |- *.
tauto.
assert (expf (L m one x y) x t).
unfold expf in |- *.
split.
simpl in |- *; unfold prec_L in |- *; tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
tauto.
split with it.
rewrite H11 in |- *.
rewrite H2 in |- *.
tauto.
apply expf_trans with x.
apply expf_symm.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- MF.upb_eq_degree in |- *.
omega.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- MF.upb_eq_degree in |- *.
omega.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
intro.
elim H3.
intro.
clear H2 H3.
decompose [and] H4.
clear H4.
unfold betweenf in H2.
unfold MF.between in H2.
simpl in H; unfold prec_L in H.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
tauto.
elim H2.
intros iz Hi.
elim Hi.
intros j1 Hj.
decompose [and] Hj.
clear Hi Hj H2.
unfold betweenf in H3.
unfold MF.between in H3.
elim H3.
intros it Hi.
elim Hi.
intros j2 Hj.
decompose [and] Hj.
clear Hj Hi H3.
assert (j1 = j2).
apply (MF.unicity_mod_p m y_1).
tauto.
tauto.
omega.
omega.
rewrite H10 in |- *.
tauto.
assert (MF.f = cF).
tauto.
assert (MF.f_1 = cF_1).
tauto.
assert (Iter (MF.f m) iz y_1 = z).
tauto.
rename H14 into E1.
assert (Iter (MF.f m) it y_1 = t).
tauto.
rename H14 into E2.
assert (MF.Iter_upb m y_1 = MF.degree m y_1).
apply MF.upb_eq_degree.
tauto.
tauto.
set (p := MF.Iter_upb m y_1) in |- *.
fold p in H9.
fold p in H12.
fold p in H14.
assert (MF.expo1 m x y0).
unfold expf in H1.
generalize (MF.expo_expo1 m x y0).
tauto.
unfold MF.expo1 in H15.
decompose [and] H15.
clear H15.
elim H17.
clear H17.
intros j0 Hj0.
elim Hj0.
clear Hj0.
intros.
assert (expf m y0 y_1).
unfold y0 in |- *.
unfold y_1 in |- *.
apply (expf_y0_y_1 m x y).
tauto.
simpl in |- *.
unfold prec_L in |- *.
tauto.
assert (expf m x y_1).
apply expf_trans with y0.
tauto.
tauto.
assert (MF.Iter_upb m x = MF.Iter_upb m y_1).
apply MF.period_expo.
tauto.
unfold expf in H19.
tauto.
fold p in H20.
rewrite H20 in H15.
assert (j0 <> p - 1).
rewrite <- H20 in |- *.
intro.
rewrite H21 in H17.
rewrite <- MF.Iter_f_f_1 in H17.
simpl in H17.
rewrite MF.Iter_upb_period in H17.
rewrite H13 in H17.
assert (cA_1 m zero (cF_1 m x) = y).
rewrite H17 in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
tauto.
unfold cF_1 in H22.
rewrite cA_1_cA in H22.
tauto.
tauto.
generalize (exd_cA m one x).
tauto.
tauto.
tauto.
tauto.
tauto.
rewrite H20 in |- *.
omega.
assert (Iter (cF m) 1 y0 = y_1).
simpl in |- *.
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
tauto.
assert (Iter (cF m) 1 x10 = x).
simpl in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
fold (cF_1 m x) in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
tauto.
rewrite <- H22 in E1.
rewrite <- MF.Iter_comp in E1.
rewrite <- H17 in E1.
rewrite <- MF.Iter_comp in E1.
rewrite <- H22 in E2.
rewrite <- MF.Iter_comp in E2.
rewrite <- H17 in E2.
rewrite <- MF.Iter_comp in E2.
assert (x10 = Iter (MF.f m) (p - 1 - (j0 + 1)) y_1).
rewrite <- H22 in |- *.
rewrite <- MF.Iter_comp in |- *.
rewrite <- H17 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j0 + 1) + 1 + j0 = p - 1).
omega.
rewrite H24 in |- *.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
rewrite <- H20 in |- *.
rewrite MF.Iter_upb_period in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
fold (cF_1 m x) in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
clear H24.
omega.
assert (p - 1 - (j0 + 1) = j2).
apply (MF.unicity_mod_p m y_1).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
tauto.
rewrite <- H24 in |- *.
symmetry in |- *.
tauto.
assert (iz + 1 + j0 = j0 + 1 + iz).
omega.
rewrite H26 in E1.
clear H26.
assert (it + 1 + j0 = j0 + 1 + it).
omega.
rewrite H26 in E2.
clear H26.
rewrite H11 in E1.
rewrite H11 in E2.
rewrite <- (cF_L1_y_1_x10 m x y iz j0) in E1.
rewrite <- (cF_L1_y_1_x10 m x y it j0) in E2.
fold y_1 in E1.
fold y_1 in E2.
assert (expf (L m one x y) y_1 z).
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
tauto.
split with iz.
tauto.
assert (expf (L m one x y) y_1 t).
unfold expf in |- *.
split.
simpl in |- *.
unfold prec_L in |- *.
tauto.
unfold MF.expo in |- *.
split.
simpl in |- *.
tauto.
split with it.
tauto.
apply expf_trans with y_1.
apply expf_symm.
tauto.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
assert (p = MF.degree m x).
unfold p in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold p in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
rewrite <- H26 in |- *.
omega.
assert (p = MF.degree m x).
unfold p in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold p in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
rewrite <- H26 in |- *.
omega.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
assert (p = MF.degree m x).
unfold p in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold p in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
rewrite <- H26 in |- *.
omega.
assert (p = MF.degree m x).
unfold p in |- *.
rewrite <- MF.upb_eq_degree in |- *.
fold p in |- *.
symmetry in |- *.
tauto.
tauto.
tauto.
rewrite <- H26 in |- *.
omega.
tauto.
tauto.
tauto.
tauto.
intro.
clear H3.
clear H2.
generalize (expf_dec m x z).
generalize (expf_dec m z t).
Admitted.

Lemma expf_L1_II_CNA_aux:forall (m:fmap)(x y z:dart)(i:nat), let m1 := (L m one x y) in let y0 := cA m zero y in let m1 := (L m one x y) in let t := Iter (cF m1) i z in inv_hmap m1 -> exd m z -> expf m x y0 -> ~ expf m x z -> expf (L m one x y) z t -> expf m z t.
Proof.
induction i.
simpl in |- *.
intros.
apply expf_refl.
tauto.
tauto.
simpl in |- *.
set (m1 := L m one x y) in |- *.
set (y0 := cA m zero y) in |- *.
set (t := Iter (cF m1) i z) in |- *.
intros.
assert (MF.f = cF).
tauto.
assert (expf m1 z t).
unfold expf in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
split with i.
rewrite H4 in |- *.
fold t in |- *.
tauto.
assert (expf m z t).
apply IHi.
simpl in |- *.
tauto.
tauto.
generalize (exd_cA m zero y).
unfold prec_L in H.
tauto.
tauto.
fold m1 in |- *.
fold t in |- *.
tauto.
apply expf_trans with t.
tauto.
unfold m1 in |- *.
rewrite cF_L1 in |- *.
fold y0 in |- *.
set (y_1 := cA_1 m one y) in |- *.
set (x10 := cF_1 m x) in |- *.
elim (eq_dart_dec y0 t).
intro.
rewrite a in H1.
apply expf_symm.
tauto.
elim (eq_dart_dec x10 t).
intros.
rewrite <- a in |- *.
apply expf_trans with y0.
apply expf_trans with x.
assert (x = cF m x10).
unfold x10 in |- *.
rewrite cF_cF_1 in |- *.
tauto.
tauto.
unfold prec_L in H.
tauto.
rewrite H7 in |- *.
unfold expf in |- *.
split.
tauto.
unfold MF.expo in |- *.
split.
unfold x10 in |- *.
generalize (exd_cF_1 m x).
unfold prec_L in H.
tauto.
split with 1.
simpl in |- *.
tauto.
tauto.
apply (expf_y0_y_1 m x y).
tauto.
tauto.
intros.
unfold expf in |- *.
unfold MF.expo in |- *.
split.
tauto.
split.
generalize (MF.expo_exd m z t).
unfold expf in H6.
tauto.
split with 1.
simpl in |- *.
tauto.
tauto.
Admitted.

Lemma expf_L1_II_CNA:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in expf m x y0 -> expf (L m one x y) z t -> ~ expf m x z -> expf m z t.
Proof.
intros.
assert (expf (L m one x y) z t).
tauto.
unfold expf in H2.
unfold MF.expo in H2.
decompose [and] H2.
clear H2.
elim H8.
intros i Hi.
clear H8.
rewrite <- Hi in |- *.
rewrite <- Hi in H4.
Admitted.

Lemma not_expf_L1_x_y0:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let y0 := cA m zero y in let y_1 := cA_1 m one y in expf m x y0 -> ~expf (L m one x y) x y_1.
Proof.
intros.
assert (expf m x y0).
tauto.
rename H2 into E1.
intro.
unfold expf in H1.
assert (MF.expo1 m x y0).
generalize (MF.expo_expo1 m x y0).
tauto.
unfold MF.expo1 in H3.
elim H3.
intros.
clear H3.
elim H5.
intros j0 Hj.
decompose [and] Hj.
clear H5 Hj.
set (p := MF.Iter_upb m x) in |- *.
fold p in H3.
assert (expf m y0 y_1).
apply (expf_y0_y_1 m x y).
tauto.
simpl in H.
tauto.
assert (y_1 <> x).
intro.
assert (cA m one x = y).
rewrite <- H7 in |- *.
unfold y_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
simpl in H.
unfold prec_L in H.
tauto.
simpl in H; unfold prec_L in H; tauto.
assert (y_1 = cF m y0).
unfold y0 in |- *.
unfold cF in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
simpl in H; unfold prec_L in H; tauto.
assert (Iter (MF.f m) (S j0) x = y_1).
simpl in |- *.
rewrite H6 in |- *.
symmetry in |- *.
tauto.
assert (S j0 <> p).
intro.
rewrite H10 in H9.
unfold p in H9.
rewrite MF.Iter_upb_period in H9.
symmetry in H9.
tauto.
tauto.
simpl in H; unfold prec_L in H; tauto.
set (m1 := L m one x y) in |- *.
fold m1 in H2.
assert (MF.f = cF).
tauto.
assert (expf m1 x y_1).
tauto.
unfold expf in H12.
assert (MF.expo1 m1 x y_1).
generalize (MF.expo_expo1 m1 x y_1).
tauto.
unfold MF.expo1 in H13.
elim H13.
intros.
clear H13.
elim H15.
intros i Hi.
clear H15.
elim Hi.
intros.
clear Hi.
set (p1 := MF.Iter_upb m1 x) in |- *.
fold p1 in H13.
assert (inv_hmap (L m one x y)).
tauto.
generalize (degree_L1_split m x y H16 E1).
fold y_1 in |- *.
fold m1 in |- *.
fold p in |- *.
assert (MF.Iter_upb m x = MF.degree m x).
apply (MF.upb_eq_degree m x).
tauto.
tauto.
assert (MF.Iter_upb m1 x = MF.degree m1 x).
apply (MF.upb_eq_degree m1 x).
tauto.
tauto.
intro.
assert (MF.degree m x = MF.degree m1 x + MF.degree m1 y_1).
tauto.
rewrite <- H17 in H19.
rewrite <- H18 in H19.
fold p in H19.
fold p1 in H19.
assert (p1 = j0 + 1).
unfold p1 in |- *.
rewrite H18 in |- *.
unfold m1 in |- *.
apply degree_L1_split_x_y0.
fold y0 in |- *.
symmetry in |- *.
tauto.
tauto.
rewrite <- H17 in |- *.
fold p in |- *.
omega.
fold y0 in |- *.
tauto.
assert (Iter (MF.f m) i x = y_1).
rewrite H11 in |- *.
rewrite <- (cF_L1_x_y0 m x y i j0) in |- *.
fold m1 in |- *.
rewrite <- H11 in |- *.
tauto.
tauto.
simpl in H.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H17 in |- *.
fold p in |- *.
omega.
assert (i = S j0).
apply (MF.unicity_mod_p m x).
tauto.
tauto.
fold p in |- *.
omega.
fold p in |- *.
omega.
rewrite H9 in |- *.
tauto.
absurd (i = S j0).
omega.
Admitted.

Lemma expf_L1_II_CN:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in expf m x y0 -> expf (L m one x y) z t -> ( betweenf m x z y0 /\ betweenf m x t y0 \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10 \/ ~ expf m x z /\ expf m z t ).
Proof.
intros.
elim (expf_dec m x z).
intro.
set (m1 := L m one x y) in |- *.
fold m1 in H2.
assert (inv_hmap (L m one x y)).
tauto.
simpl in H3.
unfold prec_L in H3.
assert (exd m y_1).
unfold y_1 in |- *.
generalize (exd_cA_1 m one y).
tauto.
unfold expf in H2.
decompose [and] H2.
clear H5.
assert (MF.expo1 m1 z t).
generalize (MF.expo_expo1 m1 z t).
fold m1 in H.
tauto.
unfold MF.expo1 in H5.
set (dz1 := MF.Iter_upb m1 z) in |- *.
fold dz1 in H5.
decompose [and] H5.
clear H5 H7.
assert (MF.f = cF).
tauto.
elim H8.
intros it1 Hi.
clear H8.
decompose [and] Hi.
clear Hi.
assert (MF.expo1 m x y0).
unfold expf in H1.
generalize (MF.expo_expo1 m x y0).
tauto.
assert (MF.expo1 m x z).
unfold expf in a.
generalize (MF.expo_expo1 m x z).
tauto.
unfold MF.expo1 in H9.
elim H9.
intros.
clear H11.
clear H9.
elim H12.
intros j0 Hj.
elim Hj.
intros.
clear Hj H12.
set (p := MF.Iter_upb m x) in |- *.
fold p in H9.
unfold MF.expo1 in H10.
elim H10.
intros.
clear H12.
elim H13.
intros iz Hi.
decompose [and] Hi.
clear Hi H13.
fold p in H12.
assert (p = MF.degree m x).
unfold p in |- *.
apply (MF.upb_eq_degree m x).
tauto.
tauto.
clear H10.
clear H6.
assert (j0 + 1 <> p).
intro.
assert (Iter (MF.f m) (j0 + 1) x = y_1).
assert (S j0 = j0 + 1).
omega.
rewrite <- H10 in |- *.
clear H10.
simpl in |- *.
rewrite H11 in |- *.
rewrite H5 in |- *.
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
tauto.
rewrite H6 in H10.
unfold p in H10.
rewrite MF.Iter_upb_period in H10.
assert (cA m one x = y).
rewrite H10 in |- *.
unfold y_1 in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
tauto.
set (p1 := MF.Iter_upb m1 x) in |- *.
assert (MF.Iter_upb m1 x = MF.degree m1 x).
apply (MF.upb_eq_degree m1 x).
unfold m1 in |- *.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
assert (MF.degree m x = MF.degree m1 x + MF.degree m1 y_1).
unfold m1 in |- *.
unfold y_1 in |- *.
apply degree_L1_split.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in H15.
fold p1 in H10.
rewrite <- H10 in H15.
assert (p1 = j0 + 1).
rewrite H10 in |- *.
unfold m1 in |- *.
apply degree_L1_split_x_y0.
fold y0 in |- *.
symmetry in |- *.
tauto.
tauto.
rewrite <- H13 in |- *.
omega.
fold y0 in |- *.
tauto.
elim (le_lt_dec iz j0).
intro.
assert (Iter (MF.f m1) iz x = z).
unfold m1 in |- *.
rewrite H5 in |- *.
rewrite (cF_L1_x_y0 m x y iz j0) in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
assert (p1 = dz1).
unfold p1 in |- *.
unfold dz1 in |- *.
apply MF.period_expo.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
split with iz.
tauto.
elim (le_lt_dec (iz + it1) j0).
intro.
rewrite <- H17 in H8.
rewrite <- MF.Iter_comp in H8.
assert (Iter (MF.f m) (it1 + iz) x = t).
rewrite H5 in |- *.
rewrite <- (cF_L1_x_y0 m x y (it1 + iz) j0) in |- *.
fold m1 in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *; tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
left.
unfold betweenf in |- *.
unfold MF.between in |- *.
split.
intros.
fold p in |- *.
split with iz.
split with j0.
split.
tauto.
split.
tauto.
omega.
intros.
split with (it1 + iz).
split with j0.
split.
tauto.
split.
tauto.
fold p in |- *.
omega.
intro.
set (it := iz + it1 - (j0 + 1)) in |- *.
assert (Iter (MF.f m) it x = t).
rewrite H5 in |- *.
rewrite <- (cF_L1_x_y0 m x y it j0) in |- *.
fold m1 in |- *.
unfold it in |- *.
rewrite <- H16 in |- *.
rewrite <- H5 in |- *.
rewrite <- (MF.Iter_plus_inv m1 x p1 (iz + it1 - p1)) in |- *.
assert (p1 + (iz + it1 - p1) = iz + it1).
omega.
rewrite H19 in |- *.
clear H19.
rewrite plus_comm in |- *.
rewrite MF.Iter_comp in |- *.
rewrite H17 in |- *.
tauto.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
unfold p1 in |- *.
rewrite MF.Iter_upb_period in |- *.
tauto.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
unfold it in |- *.
omega.
left.
unfold betweenf in |- *.
unfold MF.between in |- *.
fold p in |- *.
split.
intros.
split with iz.
split with j0.
split.
tauto.
split.
tauto.
omega.
intros.
split with it.
split with j0.
split.
tauto.
split.
tauto.
unfold it in |- *.
omega.
intro.
assert (Iter (MF.f m1) (iz - (j0 + 1)) y_1 = z).
unfold m1 in |- *.
rewrite H5 in |- *.
unfold y_1 in |- *.
rewrite (cF_L1_y_1_x10 m x y (iz - (j0 + 1)) j0) in |- *.
assert (j0 + 1 + (iz - (j0 + 1)) = iz).
omega.
rewrite H17 in |- *.
clear H17.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
rewrite <- H13 in |- *.
omega.
set (p2 := MF.Iter_upb m1 y_1) in |- *.
assert (p2 = MF.degree m1 y_1).
unfold p2 in |- *.
apply (MF.upb_eq_degree m1).
tauto.
tauto.
rewrite <- H18 in H15.
assert (p2 = dz1).
unfold p1 in |- *.
unfold dz1 in |- *.
unfold p2 in |- *.
apply MF.period_expo.
tauto.
unfold MF.expo in |- *.
split.
unfold m1 in |- *.
simpl in |- *.
tauto.
split with (iz - (j0 + 1)).
tauto.
set (iz1 := iz - (j0 + 1)) in |- *.
elim (le_lt_dec (iz + it1) (p - 1)).
intro.
rewrite <- H17 in H8.
rewrite <- MF.Iter_comp in H8.
fold iz1 in H8.
assert (Iter (MF.f m) (j0 + 1 + (it1 + iz1)) x = t).
rewrite H5 in |- *.
rewrite <- (cF_L1_y_1_x10 m x y (it1 + iz1) j0) in |- *.
fold y_1 in |- *.
fold m1 in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
fold y0 in |- *.
fold y0 in |- *.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *; tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
rewrite <- H13 in |- *.
unfold iz1 in |- *.
omega.
assert (Iter (MF.f m) (S j0) x = y_1).
simpl in |- *.
rewrite H11 in |- *.
rewrite H5 in |- *.
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
tauto.
assert (j0 + 1 + (it1 + iz1) = it1 + iz1 + S j0).
omega.
rewrite H22 in H20.
clear H22.
assert (iz = iz1 + S j0).
unfold iz1 in |- *.
omega.
rewrite H22 in H14.
rewrite MF.Iter_comp in H14.
rewrite H21 in H14.
rewrite MF.Iter_comp in H20.
rewrite H21 in H20.
right.
left.
unfold betweenf in |- *.
assert (p = MF.Iter_upb m y_1).
unfold p in |- *.
apply MF.period_expo.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with (S j0).
tauto.
unfold MF.between in |- *.
split.
intros.
rewrite <- H23 in |- *.
split with iz1.
split with (p - 1 - (j0 + 1)).
split.
tauto.
split.
rewrite <- H21 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j0 + 1) + S j0 = p - 1).
omega.
rewrite H26 in |- *.
clear H26.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
fold (cF_1 m x) in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
unfold iz1 in |- *.
omega.
intros.
split with (it1 + iz1).
split with (p - 1 - (j0 + 1)).
rewrite <- H23 in |- *.
split.
tauto.
split.
rewrite <- H21 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j0 + 1) + S j0 = p - 1).
omega.
rewrite H26 in |- *.
clear H26.
rewrite <- MF.Iter_f_f_1 in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
simpl in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
fold (cF_1 m x) in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
omega.
unfold iz1 in |- *.
intro.
assert (Iter (MF.f m1) (it1 + (iz - (j0 + 1))) y_1 = t).
rewrite MF.Iter_comp in |- *.
rewrite H17 in |- *.
tauto.
assert (Iter (MF.f m1) (it1 + (iz - (j0 + 1)) - p2) y_1 = t).
rewrite <- (MF.Iter_plus_inv m1 y_1 p2 (it1 + (iz - (j0 + 1)) - p2)) in |- *.
assert (p2 + (it1 + (iz - (j0 + 1)) - p2) = it1 + (iz - (j0 + 1))).
omega.
rewrite H21 in |- *.
tauto.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
unfold p2 in |- *.
apply MF.Iter_upb_period.
tauto.
unfold m1 in |- *.
simpl in |- *.
tauto.
assert (Iter (MF.f m) (j0 + 1 + (iz - (j0 + 1))) x = z).
rewrite H5 in |- *.
rewrite <- (cF_L1_y_1_x10 m x y (iz - (j0 + 1)) j0) in |- *.
fold y_1 in |- *.
fold m1 in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
rewrite <- H13 in |- *.
omega.
assert (Iter (MF.f m) (j0 + 1 + (it1 + (iz - (j0 + 1)) - p2)) x = t).
rewrite H5 in |- *.
rewrite <- (cF_L1_y_1_x10 m x y (it1 + (iz - (j0 + 1)) - p2) j0) in |- *.
fold y_1 in |- *.
fold m1 in |- *.
rewrite <- H5 in |- *.
tauto.
tauto.
unfold m1 in H.
unfold prec_L in |- *.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
fold y0 in |- *.
tauto.
rewrite <- H13 in |- *.
omega.
rewrite <- H13 in |- *.
omega.
right.
left.
assert (Iter (MF.f m) (j0 + 1) x = y_1).
assert (S j0 = j0 + 1).
omega.
rewrite <- H24 in |- *.
clear H24.
simpl in |- *.
rewrite H11 in |- *.
rewrite H5 in |- *.
unfold cF in |- *.
unfold y0 in |- *.
rewrite cA_1_cA in |- *.
fold y_1 in |- *.
tauto.
tauto.
tauto.
assert (j0 + 1 + (iz - (j0 + 1)) = iz - (j0 + 1) + (j0 + 1)).
omega.
rewrite H25 in H22.
clear H25.
assert (j0 + 1 + (it1 + (iz - (j0 + 1)) - p2) = it1 + (iz - (j0 + 1)) - p2 + (j0 + 1)).
omega.
rewrite H25 in H23.
clear H25.
rewrite MF.Iter_comp in H23.
rewrite H24 in H23.
rewrite MF.Iter_comp in H22.
rewrite H24 in H22.
assert (Iter (MF.f m) (p - 1 - (j0 + 1)) y_1 = x10).
rewrite <- H24 in |- *.
rewrite <- MF.Iter_comp in |- *.
assert (p - 1 - (j0 + 1) + (j0 + 1) = p - 1).
omega.
rewrite H25 in |- *.
clear H25.
rewrite <- MF.Iter_f_f_1 in |- *.
simpl in |- *.
unfold p in |- *.
rewrite MF.Iter_upb_period in |- *.
assert (MF.f_1 = cF_1).
tauto.
rewrite H25 in |- *.
unfold cF_1 in |- *.
unfold x10 in |- *.
unfold x1 in |- *.
tauto.
tauto.
tauto.
tauto.
tauto.
omega.
assert (p = MF.Iter_upb m y_1).
unfold p in |- *.
apply MF.period_expo.
tauto.
unfold MF.expo in |- *.
split.
tauto.
split with (j0 + 1).
tauto.
unfold betweenf in |- *.
unfold MF.between in |- *.
split.
intros.
rewrite <- H26 in |- *.
split with (iz - (j0 + 1)).
split with (p - 1 - (j0 + 1)).
split.
tauto.
split.
tauto.
omega.
intros.
rewrite <- H26 in |- *.
split with (it1 + (iz - (j0 + 1)) - p2).
split with (p - 1 - (j0 + 1)).
split.
tauto.
split.
tauto.
omega.
intro.
right.
right.
split.
tauto.
Admitted.

Theorem expf_L1_CNS:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> (expf (L m one x y) z t <-> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in if expf_dec m x y0 then betweenf m x z y0 /\ betweenf m x t y0 \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10 \/ ~ expf m x z /\ expf m z t else expf m z t \/ expf m z x /\ expf m t y0 \/ expf m t x /\ expf m z y0).
Proof.
intros.
split.
intros.
unfold y0 in |- *; unfold y_1 in |- *; unfold x10 in |- *; unfold x1 in |- *.
elim (expf_dec m x (cA m zero y)).
intro.
apply (expf_L1_II_CN m x y z t H H0 a H1).
intro.
apply (expf_L1_I_CN m x y z t H H0 b H1).
simpl in |- *.
elim (expf_dec m x (cA m zero y)).
intros.
apply (expf_L1_II_CS m x y z t H H0 a H1).
intro.
intro.
Admitted.

Theorem expf_L1_CN:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> expf (L m one x y) z t -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in if expf_dec m x y0 then betweenf m x z y0 /\ betweenf m x t y0 \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10 \/ ~ expf m x z /\ expf m z t else expf m z t \/ expf m z x /\ expf m t y0 \/ expf m t x /\ expf m z y0.
Proof.
intros.
generalize (expf_L1_CNS m x y z t H H0).
Admitted.

Theorem expf_L1_CS:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in (if expf_dec m x y0 then betweenf m x z y0 /\ betweenf m x t y0 \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10 \/ ~ expf m x z /\ expf m z t else expf m z t \/ expf m z x /\ expf m t y0 \/ expf m t x /\ expf m z y0) -> expf (L m one x y) z t.
Proof.
intros.
generalize (expf_L1_CNS m x y z t H H0).
Admitted.

Theorem degree_L1_split: forall(m:fmap)(x y:dart), let m1:= L m one x y in let y0 := cA m zero y in let y_1:= cA_1 m one y in inv_hmap (L m one x y) -> expf m x y0 -> MF.degree m x = MF.degree m1 x + MF.degree m1 y_1.
Proof.
intros.
assert (MF.expo1 m x y0).
unfold expf in H0.
assert (exd m x).
unfold MF.expo in H0.
tauto.
generalize (MF.expo_expo1 m x y0).
tauto.
unfold MF.expo1 in H1.
decompose [and] H1.
clear H1.
elim H3.
intros j Hj.
clear H3.
elim Hj.
clear Hj.
intros.
set (dx := MF.Iter_upb m x) in |- *.
fold dx in H1.
assert (dx = MF.degree m x).
unfold dx in |- *.
apply MF.upb_eq_degree.
simpl in H.
tauto.
tauto.
assert (0 < dx).
unfold dx in |- *.
apply MF.upb_pos.
tauto.
assert (j <> dx - 1).
intro.
rewrite H6 in H3.
rewrite <- MF.Iter_f_f_1 in H3.
simpl in H3.
unfold dx in H3.
rewrite MF.Iter_upb_period in H3.
assert (MF.f_1 = cF_1).
tauto.
rewrite H7 in H3.
unfold cF_1 in H3.
unfold y0 in H3.
assert (cA_1 m zero (cA m zero (cA m one x)) = y).
rewrite H3 in |- *.
rewrite cA_1_cA in |- *.
tauto.
simpl in H.
tauto.
simpl in H; unfold prec_L in H.
tauto.
rewrite cA_1_cA in H8.
simpl in H.
unfold prec_L in H.
tauto.
simpl in H; unfold prec_L in H.
tauto.
generalize (exd_cA m one x).
simpl in H; unfold prec_L in H.
tauto.
simpl in H; unfold prec_L in H.
tauto.
tauto.
simpl in H; unfold prec_L in H.
tauto.
tauto.
omega.
unfold m1 in |- *.
unfold y_1 in |- *.
rewrite (degree_L1_split_x_y0 m x y j) in |- *.
rewrite (degree_L1_split_y_1 m x y j) in |- *.
omega.
fold y0 in |- *.
symmetry in |- *.
tauto.
rewrite <- H4 in |- *.
omega.
fold y0 in |- *.
tauto.
tauto.
fold y0 in |- *.
symmetry in |- *.
tauto.
tauto.
rewrite <- H4 in |- *.
omega.
fold y0 in |- *.
tauto.
