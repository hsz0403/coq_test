Require Export ZArith.
Open Scope Z_scope.

Theorem Zge_sign_neg_pos: forall x y: Z, (0 >= x -> y >= 0 -> 0 >= x * y)%Z.
Proof.
intros; apply Z.le_ge; apply Zle_sign_neg_pos; auto with zarith.
