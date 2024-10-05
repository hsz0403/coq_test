Require Import Reals.
Require Import PolTac.
Open Scope R_scope.

Theorem polr_test1 x y z : x + z < y -> x + y + z < 2 * y.
Proof.
intros H.
polr H.
pols.
auto.
pols.
auto with real.
