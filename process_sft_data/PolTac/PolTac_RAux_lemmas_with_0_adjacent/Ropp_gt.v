Require Export Reals.
Open Scope R_scope.

Theorem Ropp_gt n m : m > n -> -n > -m.
Proof.
auto with real.
