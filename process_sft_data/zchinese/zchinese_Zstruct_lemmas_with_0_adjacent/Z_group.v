Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export groups.
Require Export rings.
Require Export ZArith.
Require Import Omega.
Definition IdZ (x : Z) := True.

Theorem Z_group : is_group Z IdZ Zplus 0%Z Z.opp.
Proof.
split.
red in |- *; trivial.
split.
red in |- *; auto with zarith.
split; red in |- *.
split; auto with zarith.
unfold IdZ in |- *; trivial.
split; auto with zarith.
