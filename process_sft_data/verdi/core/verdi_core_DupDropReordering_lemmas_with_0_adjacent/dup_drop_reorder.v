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

Lemma dup_drop_reorder : forall l l' : list A, (forall x, In x l' -> In x l) -> dup_drop_step_star l l'.
Proof using A_eq_dec.
induction l; intros.
-
destruct l'.
+
constructor.
+
simpl in *.
exfalso.
eauto.
-
destruct (in_dec A_eq_dec a l').
+
eapply dup_drop_step_star_remove_In.
auto.
apply IHl.
intros.
find_apply_lem_hyp remove_In_elim.
intuition.
find_apply_hyp_hyp.
simpl in *.
intuition.
exfalso.
eauto.
+
eapply dup_drop_step_star_step_1n.
eapply DDS_drop with (xs := []).
apply IHl.
simpl in *.
intros.
find_copy_apply_hyp_hyp.
intuition.
subst.
exfalso.
eauto.
