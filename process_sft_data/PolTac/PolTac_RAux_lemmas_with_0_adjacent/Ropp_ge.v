Require Export Reals.
Open Scope R_scope.

Theorem Ropp_ge n m : m >= n -> -n >= -m.
Proof.
auto with real.
