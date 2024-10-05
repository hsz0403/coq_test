Require Export ZArith.
Open Scope Z_scope.

Theorem Zlt_pos_neg: forall x, (0 < -x -> x < 0)%Z.
Proof.
auto with zarith.
