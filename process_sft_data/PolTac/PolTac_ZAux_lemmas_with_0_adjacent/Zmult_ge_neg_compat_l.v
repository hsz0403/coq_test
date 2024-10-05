Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_ge_neg_compat_l: forall n m p : Z, (m >= n)%Z -> (0 >= p)%Z -> (p * n >= p * m)%Z.
Proof.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_ge; apply Zmult_ge_compat_l; auto with zarith.
