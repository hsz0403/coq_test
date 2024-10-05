Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect Rbar.
Require Import Rcomplements.
Require Import Lim_seq Continuity Derive Series.
Require Import Lub Hierarchy.
Open Scope R_scope.
Definition CVS_dom (fn : nat -> R -> R) (D : R -> Prop) := forall x : R, D x -> ex_finite_lim_seq (fun n => fn n x).
Definition CVU_dom (fn : nat -> R -> R) (D : R -> Prop) := forall eps : posreal, eventually (fun n => forall x : R, D x -> Rabs ((fn n x) - real (Lim_seq (fun n => fn n x))) < eps).
Definition CVU_cauchy (fn : nat -> R -> R) (D : R -> Prop) := forall eps : posreal, exists N : nat, forall (n m : nat) (x : R), D x -> (N <= n)%nat -> (N <= m)%nat -> Rabs (fn n x - fn m x) < eps.
Definition is_connected (D : R -> Prop) := forall a b x, D a -> D b -> a <= x <= b -> D x.

Lemma Dini (fn : nat -> R -> R) (a b : R) : a < b -> CVS_dom fn (fun x => a <= x <= b) -> (forall (n : nat) (x : R), a <= x <= b -> continuity_pt (fn n) x) -> (forall (x : R), a <= x <= b -> continuity_pt (fun y => Lim_seq (fun n => fn n y)) x) -> (forall (n : nat) (x y : R), a <= x -> x <= y -> y <= b -> fn n x <= fn n y) -> CVU_dom fn (fun x => a <= x <= b).
Proof.
