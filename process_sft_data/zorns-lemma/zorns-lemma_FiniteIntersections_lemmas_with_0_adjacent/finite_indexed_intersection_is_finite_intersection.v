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

Lemma finite_indexed_intersection_is_finite_intersection: forall {X:Type} (S:Family X) (J:Type) (V:J->Ensemble X), FiniteT J -> (forall j:J, In S (V j)) -> In (finite_intersections S) (IndexedIntersection V).
Proof.
intros.
induction H.
rewrite empty_indexed_intersection.
constructor.
assert (IndexedIntersection V = Intersection (IndexedIntersection (fun j:T => V (Some j))) (V None)).
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
constructor.
constructor.
trivial.
trivial.
destruct H1.
constructor.
destruct H1.
destruct a as [j|]; trivial.
rewrite H1.
constructor 3; auto.
constructor 2; trivial.
destruct H1 as [g].
assert (IndexedIntersection V = IndexedIntersection (fun x:X0 => V (f x))).
apply Extensionality_Ensembles; split; red; intros.
destruct H3.
constructor.
trivial.
destruct H3.
constructor.
intro.
rewrite <- (H2 a).
trivial.
rewrite H3; auto.
