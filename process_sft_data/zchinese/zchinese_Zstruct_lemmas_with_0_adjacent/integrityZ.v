Require Export Lci.
Require Export misc.
Require Export Arith.
Require Export groups.
Require Export rings.
Require Export ZArith.
Require Import Omega.
Definition IdZ (x : Z) := True.

Theorem integrityZ : integrity Z Zmult 0%Z.
Proof.
unfold integrity in |- *.
intros a b; elim a.
intros; left; reflexivity.
intros; right.
generalize H; clear H; simpl in |- *; case b; intros; inversion H; trivial.
intros; right.
generalize H; clear H; simpl in |- *; case b; intros; inversion H; trivial.
