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

Lemma CVU_CVS_dom (fn : nat -> R -> R) (D : R -> Prop) : CVU_dom fn D -> CVS_dom fn D.
Proof.
move => Hcvu x Hx.
exists (real (Lim_seq (fun n => fn n x))).
apply is_lim_seq_spec.
intros eps.
case: (Hcvu eps) => {Hcvu} N Hcvu.
exists N => n Hn.
by apply Hcvu.
