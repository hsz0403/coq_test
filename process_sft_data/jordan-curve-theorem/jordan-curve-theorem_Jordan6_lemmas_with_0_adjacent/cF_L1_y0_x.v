Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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
omega.
