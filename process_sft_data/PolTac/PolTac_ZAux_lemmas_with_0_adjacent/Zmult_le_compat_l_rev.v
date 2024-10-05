Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_le_compat_l_rev: forall n m p : Z, (0 < p)%Z -> (p * n <= p * m)%Z -> (n <= m)%Z.
Proof.
intros n m p H H1; case (Zle_or_lt n m); auto; intros H2.
absurd (p * n <= p * m)%Z; auto with zarith.
apply Zlt_not_le; apply Zmult_lt_compat_l; auto.
