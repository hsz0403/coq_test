Require Import PolTac.
Open Scope nat_scope.

Theorem pols_test3 x y : x * x < y * y -> (x + y) * (x + y) < 2 * (x * y + y * y).
Proof.
intros.
pols.
auto.
