Require Import ZArith.
Require Import PolTac.
Open Scope Z_scope.

Theorem pols_test3 x y : 0 < y * y -> (x + y) * (x - y) < x * x.
Proof.
intros.
pols.
auto with zarith.
