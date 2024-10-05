Require Export ZArith.
Open Scope Z_scope.

Theorem Zlt_sign_neg_neg_rev: forall x y: Z, (x < 0 -> 0 < x * y -> y < 0)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (0 < x * y)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_neg_pos; auto with zarith.
