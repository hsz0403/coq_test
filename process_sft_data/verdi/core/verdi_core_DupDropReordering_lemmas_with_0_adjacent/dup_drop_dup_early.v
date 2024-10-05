Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Permutation.
Require Import StructTact.StructTactics.
Require Import Verdi.Net.
Section dup_drop_reorder.
Variable A : Type.
Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.
Inductive dup_drop_step : list A -> list A -> Prop := | DDS_dup : forall l p, In p l -> dup_drop_step l (p :: l) | DDS_drop : forall xs p ys, dup_drop_step (xs ++ p :: ys) (xs ++ ys).
Definition dup_drop_step_star := clos_refl_trans_n1 _ dup_drop_step.
End dup_drop_reorder.
Section step_failure_dup_drop_step.
Context `{params : FailureParams}.
End step_failure_dup_drop_step.

Lemma dup_drop_dup_early : forall l l' a, dup_drop_step_star l l' -> In a l -> dup_drop_step_star l (a :: l').
Proof using.
induction 1; intros.
-
apply dup_drop_step_star_step_1.
constructor.
auto.
-
concludes.
eapply dup_drop_step_star_trans; eauto.
apply dup_drop_cons.
apply dup_drop_step_star_step_1.
auto.
