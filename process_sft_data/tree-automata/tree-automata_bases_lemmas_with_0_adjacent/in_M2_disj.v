Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma in_M2_disj : forall (A : Set) (a : A) (m0 m1 : Map A), (exists c : ad, MapGet A (M2 A m0 m1) c = Some a) -> (exists c : ad, MapGet A m0 c = Some a) \/ (exists c : ad, MapGet A m1 c = Some a).
Proof.
intros.
elim H.
simple induction x.
simpl in |- *.
intro.
left.
split with N0.
assumption.
simple induction p.
intros.
right.
simpl in H1.
split with (Npos p0).
assumption.
intros.
left.
simpl in H1.
split with (Npos p0).
assumption.
intros.
right.
simpl in H0.
split with N0.
assumption.
