Require Import ZArith.
Require Import PolTac.
Open Scope Z_scope.

Theorem pols_test4 x y : x * x < y * y -> (x + y) * (x + y) < 2 * (x * y + y * y).
Proof.
intros.
pols.
auto.
