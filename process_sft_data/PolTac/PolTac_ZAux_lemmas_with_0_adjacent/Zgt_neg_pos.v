Require Export ZArith.
Open Scope Z_scope.

Theorem Zgt_neg_pos: forall x, (0 > -x -> x > 0)%Z.
Proof.
auto with zarith.
