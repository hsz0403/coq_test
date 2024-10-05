Require Export Reals.
Open Scope R_scope.

Theorem Rgt_neg_pos x : 0 > -x -> x > 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
now apply Ropp_lt_contravar; rewrite Ropp_0; auto with real.
