Require Export ZArith.
Open Scope Z_scope.

Theorem Zge_neg_pos: forall x, (0 >= -x -> x >= 0)%Z.
Proof.
auto with zarith.
