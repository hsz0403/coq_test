Require Import PolTac.
Open Scope nat_scope.

Theorem pols_test2 x y : y < 0 -> x + y < x.
Proof.
intros.
pols.
auto.
