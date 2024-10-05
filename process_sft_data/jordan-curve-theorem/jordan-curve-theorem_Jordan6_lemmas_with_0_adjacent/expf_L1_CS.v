Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Theorem expf_L1_CS:forall (m:fmap)(x y z t:dart), inv_hmap (L m one x y) -> exd m z -> let x1 := cA m one x in let x10 := cA m zero x1 in let y0 := cA m zero y in let y_1 := cA_1 m one y in (if expf_dec m x y0 then betweenf m x z y0 /\ betweenf m x t y0 \/ betweenf m y_1 z x10 /\ betweenf m y_1 t x10 \/ ~ expf m x z /\ expf m z t else expf m z t \/ expf m z x /\ expf m t y0 \/ expf m t x /\ expf m z y0) -> expf (L m one x y) z t.
Proof.
intros.
generalize (expf_L1_CNS m x y z t H H0).
tauto.
