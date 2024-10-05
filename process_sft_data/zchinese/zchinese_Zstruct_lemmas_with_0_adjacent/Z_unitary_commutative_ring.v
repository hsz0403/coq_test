Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export groups.
Require Export rings.
Require Export ZArith.
Require Import Omega.
Definition IdZ (x : Z) := True.

Theorem Z_unitary_commutative_ring : is_unitary_commutative_ring Z IdZ Zplus Zmult 0%Z 1%Z Z.opp.
Proof.
unfold is_unitary_commutative_ring in |- *.
split.
exact Z_ring.
split.
red in |- *; auto with zarith.
split.
unfold IdZ in |- *; trivial.
split; auto with zarith.
