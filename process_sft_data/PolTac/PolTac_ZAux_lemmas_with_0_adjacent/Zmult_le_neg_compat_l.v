Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_le_neg_compat_l: forall n m p : Z, (m <= n)%Z -> (p <= 0)%Z -> (p * n <= p * m)%Z.
Proof.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_le; apply Zmult_le_compat_l; auto with zarith.
