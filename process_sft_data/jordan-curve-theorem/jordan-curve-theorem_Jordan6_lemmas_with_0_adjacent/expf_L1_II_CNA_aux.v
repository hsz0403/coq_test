Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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
tauto.
