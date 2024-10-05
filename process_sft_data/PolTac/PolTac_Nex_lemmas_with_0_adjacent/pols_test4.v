Require Import NArith.
Require Import PolTac.
Open Scope N_scope.

Theorem pols_test4 x y z : x + y * (y + z) = 2 * z -> 2 * x + y * (y + z) = x + z + z.
Proof.
intros.
pols.
auto.
