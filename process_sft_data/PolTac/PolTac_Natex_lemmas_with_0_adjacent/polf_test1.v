Require Import PolTac.
Open Scope nat_scope.

Theorem polf_test1 x y : 1 <= y -> x <= x * y.
Proof.
intros.
polf.
