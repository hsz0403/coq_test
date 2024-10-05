Require Export Reals.
Open Scope R_scope.

Theorem Rplus_neg_compat_l a b c : b <> c -> a + b <> a + c.
Proof.
now intros * H; contradict H; apply Rplus_eq_reg_l with a.
