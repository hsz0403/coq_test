Require Export ZArith.
Open Scope Z_scope.

Theorem Zge_sign_neg_neg_rev: forall x y: Z, (0 > x -> x * y >= 0 -> 0 >= y)%Z.
Proof.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_neg_neg_rev with x; auto with zarith.
