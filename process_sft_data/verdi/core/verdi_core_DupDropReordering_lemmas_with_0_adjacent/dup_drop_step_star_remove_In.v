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

Lemma dup_drop_step_star_remove_In : forall l' l a, In a l' -> dup_drop_step_star l (remove A_eq_dec a l') -> dup_drop_step_star (a :: l) l'.
Proof using.
induction l'; simpl; intuition.
-
subst.
break_if; try congruence.
destruct (in_dec A_eq_dec a0 l').
+
find_apply_hyp_hyp.
eapply dup_drop_step_star_trans; eauto.
eapply dup_drop_step_star_step_1.
apply DDS_dup; auto.
+
rewrite remove_not_in_nop in * by auto.
apply dup_drop_cons.
auto.
-
break_if.
+
subst.
find_apply_hyp_hyp.
eapply dup_drop_step_star_trans; eauto.
eapply dup_drop_step_star_step_1.
apply DDS_dup; auto.
+
pose proof dup_drop_in l _ a ltac:(eauto).
try concludes.
eapply dup_drop_step_star_step_n1 in H0; [| eapply DDS_drop with (xs := [])].
simpl in *.
apply IHl' in H0; auto.
apply dup_drop_dup_early; auto.
simpl.
intuition.
