Require Export ZArith.
Open Scope Z_scope.

Theorem Zlt_sign_pos_neg_rev: forall x y: Z, (0 < x -> x * y < 0 -> y < 0)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (x * y < 0)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_pos_pos; auto with zarith.
