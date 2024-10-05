Require Export ZArith.
Open Scope Z_scope.

Theorem Zopp_gt: forall n m, (m > n -> -n > -m)%Z.
Proof.
auto with zarith.
