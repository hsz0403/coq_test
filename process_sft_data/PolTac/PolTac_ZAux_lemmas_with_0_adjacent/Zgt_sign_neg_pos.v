Require Export ZArith.
Open Scope Z_scope.

Theorem Zgt_sign_neg_pos: forall x y: Z, (0 > x -> y > 0 -> 0> x * y)%Z.
Proof.
intros; apply Z.lt_gt; apply Zlt_sign_neg_pos; auto with zarith.
