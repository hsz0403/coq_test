Require Import Reals.
Require Import PolTac.
Open Scope R_scope.

Theorem pols_test4 x y : x * x < y * y -> (x + y) * (x + y) < 2 * (x * y + y * y).
Proof.
intros.
pols.
auto.
