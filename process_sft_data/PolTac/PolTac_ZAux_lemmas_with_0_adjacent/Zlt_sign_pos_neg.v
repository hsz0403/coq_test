Require Export ZArith.
Open Scope Z_scope.

Theorem Zlt_sign_pos_neg: forall x y: Z, (0 < x -> y < 0 -> x * y < 0)%Z.
Proof.
intros x y H1 H2; apply Zlt_pos_neg; replace (- (x * y))%Z with (x * (- y))%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
