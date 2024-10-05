Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_ge_neg_compat_l_rev: forall n m p : Z, (0 > p)%Z -> (p * n >= p * m)%Z -> (m >= n)%Z.
Proof.
intros n m p H H1; apply Z.le_ge; apply Zmult_le_neg_compat_l_rev with p; auto with zarith.
