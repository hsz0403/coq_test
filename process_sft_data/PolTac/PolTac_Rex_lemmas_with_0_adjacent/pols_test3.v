Require Import Reals.
Require Import PolTac.
Open Scope R_scope.

Theorem pols_test3 x y : 0 < y * y -> (x + y) * (x - y) < x * x.
Proof.
intros.
pols.
auto with real.
