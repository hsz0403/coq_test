Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_ge_compat_l_rev: forall n m p : Z, (p > 0)%Z -> (p * n >= p * m)%Z -> (n >= m)%Z.
Proof.
intros n m p H H1; apply Z.le_ge; apply Zmult_le_compat_l_rev with p; auto with zarith.
