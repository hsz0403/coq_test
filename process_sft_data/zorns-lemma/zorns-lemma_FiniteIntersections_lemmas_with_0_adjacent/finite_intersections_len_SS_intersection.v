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

Lemma finite_intersections_len_SS_intersection {X : Type} {F : Family X} {U : Ensemble X} (n : nat) : In (finite_intersections_len F (S (S n))) U -> exists m k V W, In (finite_intersections_len F (S m)) V /\ In (finite_intersections_len F (S k)) W /\ U = Intersection V W /\ n = m + k.
Proof.
intro H.
red in H.
dependent induction H.
-
destruct m, k; discriminate + injection x as x; subst.
+
rewrite (finite_intersections_len_0_full_set H), Intersection_Full_set.
now apply IHfinite_intersections_len0.
+
rewrite (finite_intersections_len_0_full_set H0), Intersection_commutative, Intersection_Full_set.
apply IHfinite_intersections_len.
lia.
+
exists m, k, U, V.
repeat split; lia + assumption.
