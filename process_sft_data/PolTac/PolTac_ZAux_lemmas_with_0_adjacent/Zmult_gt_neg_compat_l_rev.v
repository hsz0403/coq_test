Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_gt_neg_compat_l_rev: forall n m p : Z, (0 > p)%Z -> (p * n > p * m)%Z -> (m > n)%Z.
Proof.
intros n m p H H1; apply Z.lt_gt; apply Zmult_lt_neg_compat_l_rev with p; auto with zarith.
