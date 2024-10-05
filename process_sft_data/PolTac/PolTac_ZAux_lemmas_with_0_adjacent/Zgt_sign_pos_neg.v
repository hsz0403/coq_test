Require Export ZArith.
Open Scope Z_scope.

Theorem Zgt_sign_pos_neg: forall x y: Z, (x > 0 -> 0 > y -> 0 > x * y)%Z.
Proof.
intros; apply Z.lt_gt; apply Zlt_sign_pos_neg; auto with zarith.
