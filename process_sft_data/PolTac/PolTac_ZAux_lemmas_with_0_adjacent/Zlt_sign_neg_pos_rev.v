Require Export ZArith.
Open Scope Z_scope.

Theorem Zlt_sign_neg_pos_rev: forall x y: Z, (x < 0 -> x * y < 0 -> 0 < y)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (x * y < 0)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_neg_neg; auto with zarith.
