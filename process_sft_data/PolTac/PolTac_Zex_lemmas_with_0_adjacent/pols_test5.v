Require Import ZArith.
Require Import PolTac.
Open Scope Z_scope.

Theorem pols_test5 x y z : x + y * (y + z) = 2 * z -> 2 * x + y * (y + z) = (x + z) + z.
Proof.
intros.
pols.
auto.
