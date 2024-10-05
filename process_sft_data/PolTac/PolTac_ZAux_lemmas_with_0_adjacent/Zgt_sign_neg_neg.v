Require Export ZArith.
Open Scope Z_scope.

Theorem Zgt_sign_neg_neg: forall x y: Z, (0 > x -> 0 > y -> x * y > 0)%Z.
Proof.
intros; apply Z.lt_gt; apply Zlt_sign_neg_neg; auto with zarith.
