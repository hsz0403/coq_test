Require Import ZArith.
Require Import PolTac.
Open Scope Z_scope.

Theorem polf_test2 x y : 0 < x -> x <= x * y -> 1 <= y.
Proof.
intros H1 H2.
hyp_polf H2.
