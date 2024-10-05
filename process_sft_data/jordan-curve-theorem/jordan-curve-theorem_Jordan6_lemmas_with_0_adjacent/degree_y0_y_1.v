Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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
tauto.
