Require Export ZArith.
Open Scope Z_scope.

Theorem Zplus_ge_reg_l: forall n m p : Z, (p + n >= p + m -> n >= m)%Z.
Proof.
intros n m p H; apply Z.le_ge; apply Zplus_le_reg_l with p; auto; apply Z.ge_le; auto.
