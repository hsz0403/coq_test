Require Export ZArith.
Open Scope Z_scope.

Theorem Zgt_sign_pos_pos_rev: forall x y: Z, (x > 0 -> x * y > 0 -> y > 0)%Z.
Proof.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_pos_pos_rev with x; auto with zarith.
