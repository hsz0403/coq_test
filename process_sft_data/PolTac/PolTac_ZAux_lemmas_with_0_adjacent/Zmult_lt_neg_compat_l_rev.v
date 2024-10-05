Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_lt_neg_compat_l_rev: forall n m p : Z, (p < 0)%Z -> (p * n < p * m)%Z -> (m < n)%Z.
Proof.
intros n m p H H1; case (Zle_or_lt n m); auto; intros H2.
absurd (p * n < p * m)%Z; auto with zarith.
apply Zle_not_lt; apply Zmult_le_neg_compat_l; auto with zarith.
