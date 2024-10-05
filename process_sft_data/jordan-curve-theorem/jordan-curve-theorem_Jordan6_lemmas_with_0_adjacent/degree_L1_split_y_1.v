Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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
tauto.
