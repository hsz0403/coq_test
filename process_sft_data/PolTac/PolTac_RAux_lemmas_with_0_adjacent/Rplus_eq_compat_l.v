Require Export Reals.
Open Scope R_scope.

Theorem Rplus_eq_compat_l a b c : b = c -> a + b = a + c.
Proof.
congruence.
