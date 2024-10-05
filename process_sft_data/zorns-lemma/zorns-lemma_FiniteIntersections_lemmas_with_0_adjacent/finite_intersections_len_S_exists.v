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

Lemma finite_intersections_len_S_exists {X : Type} {F : Family X} {U : Ensemble X} {n : nat} : In (finite_intersections_len F (S n)) U -> exists V W, In (finite_intersections_len F n) V /\ In (finite_intersections_len F 1) W /\ U = Intersection V W.
Proof.
generalize dependent U.
generalize dependent n.
apply (well_founded_ind lt_wf (fun n => forall U, In (finite_intersections_len F (S n)) U -> exists V W, In (finite_intersections_len F n) V /\ In (finite_intersections_len F 1) W /\ U = Intersection V W)).
intros [|n] IH U H.
-
apply finite_intersections_len_1_in in H.
exists Full_set, U.
now repeat split; constructor + rewrite Intersection_Full_set.
-
apply finite_intersections_len_SS_intersection in H.
destruct H as [m [[|k] [V [W [HV [HW [eq1 eq2]]]]]]].
+
rewrite Nat.add_0_r in eq2.
subst.
now exists V, W.
+
apply IH in HV; [|lia].
destruct HV as [V1 [V2 [HV1 [HV2 eq3]]]].
rewrite eq2, plus_n_Sm.
exists (Intersection V1 W), V2.
repeat (constructor; try easy).
subst.
now rewrite (Intersection_associative V1 W), (Intersection_commutative _ W), <- (Intersection_associative V1).
