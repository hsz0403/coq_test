Require Export Reals.
Open Scope R_scope.

Theorem Rplus_neg_reg_l a b c : a + b <> a + c -> b <> c.
Proof.
congruence.
