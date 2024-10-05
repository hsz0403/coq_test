Require Import Reals.
Require Import PolTac.
Open Scope R_scope.

Theorem pols_test5 x y z : x * (z + 2) < y * (2 * x + 1) -> x * (z + y + 2) < y * (3 * x + 1).
Proof.
intros.
pols.
auto.
