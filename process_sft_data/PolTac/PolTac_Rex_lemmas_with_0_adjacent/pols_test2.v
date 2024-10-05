Require Import Reals.
Require Import PolTac.
Open Scope R_scope.

Theorem pols_test2 x y : 0 < y -> x < x + y.
Proof.
intros.
pols.
auto.
