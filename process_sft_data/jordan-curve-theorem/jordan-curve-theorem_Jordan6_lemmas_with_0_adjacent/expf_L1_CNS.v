Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

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
apply (expf_L1_I_CS m x y z t H H0 b H1).
