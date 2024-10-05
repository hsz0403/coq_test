Require Import ZArith.
Require Import PolTac.
Open Scope Z_scope.

Theorem pols_test1 x y : x < y -> x + x < y + x.
Proof.
intros.
pols.
Admitted.

Theorem pols_test2 x y : y < 0 -> x + y < x.
Proof.
intros.
pols.
Admitted.

Theorem pols_test3 x y : 0 < y * y -> (x + y) * (x - y) < x * x.
Proof.
intros.
pols.
Admitted.

Theorem pols_test4 x y : x * x < y * y -> (x + y) * (x + y) < 2 * (x * y + y * y).
Proof.
intros.
pols.
Admitted.

Theorem polf_test1 x y : 0 <= x -> 1 <= y -> x <= x * y.
Proof.
intros.
Admitted.

Theorem polf_test2 x y : 0 < x -> x <= x * y -> 1 <= y.
Proof.
intros H1 H2.
Admitted.

Theorem polr_test1 x y z : x + z < y -> x + y + z < 2 * y.
Proof.
intros H.
polr H.
pols.
auto.
pols.
Admitted.

Theorem pols_test5 x y z : x + y * (y + z) = 2 * z -> 2 * x + y * (y + z) = (x + z) + z.
Proof.
intros.
pols.
auto.
