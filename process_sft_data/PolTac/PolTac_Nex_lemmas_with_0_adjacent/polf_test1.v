Require Import NArith.
Require Import PolTac.
Open Scope N_scope.

Theorem polf_test1 x y : 1 <= y -> x <= x * y.
Proof.
intros.
polf.
