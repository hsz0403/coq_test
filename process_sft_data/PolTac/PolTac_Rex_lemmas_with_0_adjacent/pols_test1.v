Require Import Reals.
Require Import PolTac.
Open Scope R_scope.

Theorem pols_test1 x y : x < y -> x + x < y + x.
Proof.
intros.
pols.
auto.
