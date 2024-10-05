Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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
apply (expf_not_orbit_x_aux m x y z i H H6 H1 H2).
