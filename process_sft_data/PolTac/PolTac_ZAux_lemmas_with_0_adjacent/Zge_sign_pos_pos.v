Require Export ZArith.
Open Scope Z_scope.

Theorem Zge_sign_pos_pos: forall x y: Z, (x >= 0 -> y >= 0 -> x * y >= 0)%Z.
Proof.
intros; apply Z.le_ge; apply Zle_sign_pos_pos; auto with zarith.
