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

Lemma finite_intersections_len_union {X : Type} (F : Family X) : IndexedUnion (finite_intersections_len F) = finite_intersections F.
Proof.
apply Extensionality_Ensembles.
split.
-
intros ? [n U HU].
red in HU.
dependent induction HU.
+
apply intro_full.
+
now apply intro_S.
+
now apply intro_intersection.
-
intros ? HU.
red in HU.
dependent induction HU; try destruct IHHU, IHHU0; econstructor.
+
constructor.
+
now apply intro_fi_len_S.
+
apply intro_fi_len_intersection.
exact H1.
exact H2.
