Require Export ZArith.
Open Scope Z_scope.

Theorem Zle_sign_neg_pos: forall x y: Z, (x <= 0 -> 0 <= y -> x * y <= 0)%Z.
Proof.
intros x y H1 H2; apply Zle_pos_neg; replace (- (x * y))%Z with (-x * y)%Z; auto with zarith; ring.
