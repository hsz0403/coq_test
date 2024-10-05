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
tauto.
