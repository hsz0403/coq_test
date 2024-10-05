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

Lemma finite_intersections_countable {X : Type} (F : Family X) : Countable F -> Countable (finite_intersections F).
Proof.
intros [f Hf].
rewrite <- finite_intersections_len_union.
apply countable_union.
-
apply nat_countable.
-
intro n.
induction n.
+
apply intro_nat_injection with (fun x => 0).
intros [U HU] [V HV] eq.
apply proj1_sig_injective.
simpl.
now rewrite (finite_intersections_len_0_full_set HU), (finite_intersections_len_0_full_set HV).
+
destruct (finite_intersections_len_S_choice F n) as [g Hg], IHn as [fn Hfn].
refine (inj_countable (fun U => (fn (fst (g U)), f (exist _ (proj1_sig (snd (g U))) _))) countable_nat_product _).
intros [U HU] [V HV] eq.
injection eq as eq1 eq2.
apply Hfn, proj1_sig_eq in eq1.
apply Hf, proj1_sig_eq in eq2.
apply Proj1SigInjective.proj1_sig_injective.
now rewrite Hg, Hg, eq1, eq2.
Unshelve.
destruct (snd (g U)).
now apply finite_intersections_len_1_in.
