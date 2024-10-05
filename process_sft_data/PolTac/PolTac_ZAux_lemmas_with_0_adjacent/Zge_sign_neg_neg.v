Require Export ZArith.
Open Scope Z_scope.

Theorem Zge_sign_neg_neg: forall x y: Z, (0 >= x -> 0 >= y -> x * y >= 0)%Z.
Proof.
intros; apply Z.le_ge; apply Zle_sign_neg_neg; auto with zarith.
