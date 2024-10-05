Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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
apply (expf_L1_II_CNA_aux m x y z i H H0 H1 H3 H4).
