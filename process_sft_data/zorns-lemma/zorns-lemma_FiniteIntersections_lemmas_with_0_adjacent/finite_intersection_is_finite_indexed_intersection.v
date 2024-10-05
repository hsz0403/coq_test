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

Lemma finite_intersection_is_finite_indexed_intersection: forall {X:Type} (S:Family X) (U:Ensemble X), In (finite_intersections S) U -> exists J:Type, FiniteT J /\ exists V:J->Ensemble X, (forall j:J, In S (V j)) /\ U = IndexedIntersection V.
Proof.
intros.
induction H.
exists False.
split.
constructor.
exists (False_rect _).
split.
destruct j.
symmetry; apply empty_indexed_intersection.
exists True.
split.
exact True_finite.
exists (True_rect U).
split.
destruct j.
simpl.
trivial.
apply Extensionality_Ensembles; split; red; intros.
constructor.
destruct a; simpl.
trivial.
destruct H0.
exact (H0 I).
destruct IHfinite_intersections as [J0 [? [W []]]].
destruct IHfinite_intersections0 as [J1 [? [W' []]]].
exists ((J0+J1)%type).
split.
apply finite_sum; trivial.
exists (fun s:J0+J1 => match s with | inl j => W j | inr j => W' j end).
split.
destruct j; auto.
apply Extensionality_Ensembles; split; red; intros.
destruct H7.
rewrite H3 in H7; destruct H7.
rewrite H6 in H8; destruct H8.
constructor.
destruct a as [j|j]; auto.
destruct H7.
constructor.
rewrite H3; constructor.
intro j.
exact (H7 (inl _ j)).
rewrite H6; constructor.
intro j.
exact (H7 (inr _ j)).
