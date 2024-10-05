Require Import ZArith.
Require Import PolTac.
Open Scope Z_scope.

Theorem pols_test1 x y : x < y -> x + x < y + x.
Proof.
intros.
pols.
auto.
