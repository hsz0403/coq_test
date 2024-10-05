Require Export Reals.
Open Scope R_scope.

Theorem Rmult_gt_neg_compat_l n m p : (m > n) -> (0 > p) -> (p * n > p * m).
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
auto with real.
