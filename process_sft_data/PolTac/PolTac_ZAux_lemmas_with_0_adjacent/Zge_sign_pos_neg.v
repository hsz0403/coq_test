Require Export ZArith.
Open Scope Z_scope.

Theorem Zge_sign_pos_neg: forall x y: Z, (x >= 0 -> 0 >= y -> 0 >= x * y)%Z.
Proof.
intros; apply Z.le_ge; apply Zle_sign_pos_neg; auto with zarith.
