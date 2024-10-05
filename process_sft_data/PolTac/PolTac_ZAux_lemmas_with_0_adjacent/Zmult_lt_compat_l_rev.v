Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_lt_compat_l_rev: forall n m p : Z, (0 < p)%Z -> (p * n < p * m)%Z -> (n < m)%Z.
Proof.
intros n m p H H1; case (Zle_or_lt m n); auto; intros H2.
absurd (p * n < p * m)%Z; auto with zarith.
apply Zle_not_lt; apply Zmult_le_compat_l; auto with zarith.
