Require Export ZArith.
Open Scope Z_scope.

Theorem Zlt_sign_neg_neg: forall x y: Z, (x < 0 -> y < 0 -> 0 < x * y)%Z.
Proof.
intros x y H1 H2; replace (x * y)%Z with (-x * -y)%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
