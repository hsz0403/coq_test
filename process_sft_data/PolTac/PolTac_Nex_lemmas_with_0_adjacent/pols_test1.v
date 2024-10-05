Require Import NArith.
Require Import PolTac.
Open Scope N_scope.

Theorem pols_test1 x y : x < y -> x + x < y + x.
Proof.
intros.
pols.
auto.
