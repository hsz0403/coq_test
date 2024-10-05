Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export groups.
Require Export rings.
Require Export ZArith.
Require Import Omega.
Definition IdZ (x : Z) := True.

Theorem Z_ring : is_ring Z IdZ Zplus Zmult 0%Z Z.opp.
Proof.
unfold is_ring in |- *.
split.
red in |- *; auto with zarith.
split.
exact Z_group.
split.
unfold intern in |- *.
intros.
exact I.
split; red in |- *; auto with zarith.
