Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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
tauto.
