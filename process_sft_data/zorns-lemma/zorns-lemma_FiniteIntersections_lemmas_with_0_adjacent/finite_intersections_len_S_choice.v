From Coq Require Import Program.Equality.
From Coq Require Import Lia.
From Coq Require Import ClassicalChoice.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Families.
Require Export FiniteTypes.
Require Export IndexedFamilies.
Require Export CountableTypes.
Require Import Proj1SigInjective.
Require Export Powerset_facts.
Inductive finite_intersections {X:Type} (S:Family X) : Family X := | intro_full: In (finite_intersections S) Full_set | intro_S: forall U:Ensemble X, In S U -> In (finite_intersections S) U | intro_intersection: forall U V:Ensemble X, In (finite_intersections S) U -> In (finite_intersections S) V -> In (finite_intersections S) (Intersection U V).
Section Lemmas.
Open Scope nat.
Inductive finite_intersections_len {X : Type} (F : Family X) : IndexedFamily nat (Ensemble X) := | intro_fi_len_full : In (finite_intersections_len F 0) Full_set | intro_fi_len_S : forall U : Ensemble X, In F U -> In (finite_intersections_len F 1) U | intro_fi_len_intersection : forall (U V : Ensemble X) (m k : nat), In (finite_intersections_len F m) U -> In (finite_intersections_len F k) V -> In (finite_intersections_len F (m + k)) (Intersection U V).
End Lemmas.

Lemma finite_intersections_len_S_choice {X : Type} (F : Family X) (n : nat) : exists f : {U : Ensemble X | In (finite_intersections_len F (S n)) U} -> {U : Ensemble X | In (finite_intersections_len F n) U} * {U : Ensemble X | In (finite_intersections_len F 1) U}, forall U, proj1_sig U = Intersection (proj1_sig (fst (f U))) (proj1_sig (snd (f U))).
Proof.
apply choice with (R := fun U : {U : Ensemble X | In (finite_intersections_len F (S n)) U} => fun y : {U : Ensemble X | In (finite_intersections_len F n) U} * {U : Ensemble X | In (finite_intersections_len F 1) U} => proj1_sig U = Intersection (proj1_sig (fst y)) (proj1_sig (snd y))).
intros [? HU].
destruct (finite_intersections_len_S_exists HU) as [V [W [HV [HW ?]]]].
now exists (exist _ V HV, exist _ W HW).
