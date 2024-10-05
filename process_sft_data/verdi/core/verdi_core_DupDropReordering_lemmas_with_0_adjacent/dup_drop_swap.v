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

Lemma dup_drop_swap : forall l x y, dup_drop_step_star (x :: y :: l) (y :: x :: l).
Proof using.
intros.
eapply dup_drop_step_star_step_1n; [eapply DDS_dup with (p := y); simpl; auto|].
eapply dup_drop_step_star_step_1n.
eapply DDS_drop with (xs := [y; x]) (p := y) (ys := l).
constructor.
