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

Lemma CVU_dom_Reals (fn : nat -> R -> R) (f : R -> R) (x : R) (r : posreal) : (forall y, (Boule x r y) -> (Finite (f y)) = Lim_seq (fun n => fn n y)) -> (CVU fn f x r <-> CVU_dom fn (Boule x r)).
Proof.
split ; move => Hcvu.
have Hf : forall y, Boule x r y -> is_lim_seq (fun n => fn n y) (f y).
move => y Hy.
apply is_lim_seq_spec.
move => [e He] /=.
case: (Hcvu e He) => {Hcvu} N Hcvu.
exists N => n Hn.
rewrite -Ropp_minus_distr' Rabs_Ropp.
by apply Hcvu.
move => [e He] /=.
case: (Hcvu e He) => {Hcvu} N Hcvu.
exists N => n Hn y Hy.
rewrite (is_lim_seq_unique (fun n0 : nat => fn n0 y) _ (Hf y Hy)).
simpl.
rewrite -/(Rminus (fn n y) (f y)) -Ropp_minus_distr' Rabs_Ropp.
by apply Hcvu.
move => e He ; set eps := mkposreal e He.
case: (Hcvu eps) => {Hcvu} N Hcvu.
exists N => n y Hn Hy.
move: (Hcvu n Hn y Hy).
rewrite -(H y Hy) /=.
by rewrite -Ropp_minus_distr' Rabs_Ropp.
