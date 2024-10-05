Require Export ZArith.
Open Scope Z_scope.

Theorem Zplus_ge_compat_l: forall n m p : Z, (n >= m -> p + n >= p + m)%Z.
Proof.
intros n m p H; apply Z.le_ge; apply Zplus_le_compat_l; auto; apply Z.ge_le; auto.
