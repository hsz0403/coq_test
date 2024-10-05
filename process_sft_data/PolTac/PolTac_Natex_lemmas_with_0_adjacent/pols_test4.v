Require Import PolTac.
Open Scope nat_scope.

Theorem pols_test4 x y z : x + y * (y + z) = 2 * z -> 2 * x + y * (y + z) = x + z + z.
Proof.
intros.
pols.
auto.
