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

Theorem step_failure_dup_drop_step : forall ps ps' Sigma f, dup_drop_step_star _ ps ps' -> step_failure_star (f, mkNetwork ps Sigma) (f, mkNetwork ps' Sigma) [].
Proof using.
induction 1.
-
constructor.
-
match goal with | [ H : dup_drop_step _ _ _ |- _ ] => invc H end.
+
find_apply_lem_hyp in_split.
break_exists.
break_and.
subst.
apply refl_trans_n1_1n_trace.
eapply RTn1TStep with (cs := []).
*
apply refl_trans_1n_n1_trace.
apply IHclos_refl_trans_n1.
*
eapply StepFailure_dup; [simpl; eauto|].
auto.
+
apply refl_trans_n1_1n_trace.
eapply RTn1TStep with (cs := []).
*
apply refl_trans_1n_n1_trace.
apply IHclos_refl_trans_n1.
*
eapply StepFailure_drop; [simpl; eauto|].
auto.
