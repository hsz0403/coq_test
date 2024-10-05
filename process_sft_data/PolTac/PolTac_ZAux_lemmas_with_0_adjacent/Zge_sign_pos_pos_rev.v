Require Export ZArith.
Open Scope Z_scope.

Theorem Zge_sign_pos_pos_rev: forall x y: Z, (x > 0 -> x * y >= 0 -> y >= 0)%Z.
Proof.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_pos_pos_rev with x; auto with zarith.
