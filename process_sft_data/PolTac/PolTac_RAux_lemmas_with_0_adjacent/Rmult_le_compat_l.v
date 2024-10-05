Require Export Reals.
Open Scope R_scope.

Theorem Rmult_le_compat_l n m p : m <= n -> 0 <= p -> p * m <= p * n.
Proof.
auto with real.
