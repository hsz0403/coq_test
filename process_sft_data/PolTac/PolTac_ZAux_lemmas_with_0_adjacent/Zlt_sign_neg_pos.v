Require Export ZArith.
Open Scope Z_scope.

Theorem Zlt_sign_neg_pos: forall x y: Z, (x < 0 -> 0 < y -> x * y < 0)%Z.
Proof.
intros x y H1 H2; apply Zlt_pos_neg; replace (- (x * y))%Z with (-x * y)%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
