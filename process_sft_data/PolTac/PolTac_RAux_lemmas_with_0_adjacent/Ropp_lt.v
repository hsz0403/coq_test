Require Export Reals.
Open Scope R_scope.

Theorem Ropp_lt n m : m < n -> -n < -m.
Proof.
auto with real.
