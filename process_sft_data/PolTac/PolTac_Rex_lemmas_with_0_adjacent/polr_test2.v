Require Import Reals.
Require Import PolTac.
Open Scope R_scope.

Theorem polr_test2 x y z t u : t < 0 -> y = u -> x + z < y -> 2 * y * t < x * t + t * u + z * t.
Proof.
intros H1 H2 H3.
polf.
polr H2; auto with real.
polr H3.
pols.
auto.
pols.
auto with real.
