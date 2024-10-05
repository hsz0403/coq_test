Require Import ZArith.
Require Import PolTac.
Open Scope Z_scope.

Theorem polf_test1 x y : 0 <= x -> 1 <= y -> x <= x * y.
Proof.
intros.
polf.
