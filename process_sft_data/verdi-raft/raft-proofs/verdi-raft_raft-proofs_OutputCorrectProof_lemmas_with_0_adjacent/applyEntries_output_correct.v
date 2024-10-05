Require Import Verdi.TraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.OutputCorrectInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.StateMachineCorrectInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.LogMatchingInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section OutputCorrect.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {aemi : applied_entries_monotonic_interface}.
Context {smci : state_machine_correct_interface}.
Context {si : sorted_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Context {lmi : log_matching_interface}.
Section inner.
Variable client : clientId.
Variables id : nat.
Variable out : output.
Ltac intermediate_networks := match goal with | Hdgs : doGenericServer ?h ?st' = _, Hdl : doLeader ?st ?h = _ |- context [update _ (nwState ?net) ?h ?st''] => replace st with (update name_eq_dec (nwState net) h st h) in Hdl by eauto using update_eq; replace st' with (update name_eq_dec (update name_eq_dec (nwState net) h st) h st' h) in Hdgs by eauto using update_eq; let H := fresh "H" in assert (update name_eq_dec (nwState net) h st'' = update name_eq_dec (update name_eq_dec (update name_eq_dec (nwState net) h st) h st') h st'') by (repeat rewrite update_overwrite; auto); unfold data in *; simpl in *; rewrite H; clear H end.
Program Instance TR : TraceRelation step_failure := { init := step_failure_init; T := in_output_trace client id out ; T_dec := in_output_trace_dec ; R := fun s => let (_, net) := s in output_correct client id out (applied_entries (nwState net)) }.
Next Obligation.
repeat break_let.
subst.
find_eapply_lem_hyp applied_entries_monotonic'; eauto using step_failure_star_raft_intermediate_reachable.
unfold output_correct in *.
break_exists.
repeat find_rewrite.
match goal with | [ |- context [ deduplicate_log (?l ++ ?l') ] ] => pose proof deduplicate_log_app l l'; break_exists; find_rewrite end.
repeat eexists; intuition eauto; repeat find_rewrite; auto.
rewrite app_ass.
simpl.
repeat f_equal.
Defined.
Next Obligation.
unfold in_output_trace in *.
intuition.
break_exists; intuition.
Defined.
Next Obligation.
find_apply_lem_hyp in_output_changed; auto.
eauto using in_output_trace_step_output_correct, step_failure_star_raft_intermediate_reachable.
Defined.
End inner.
Instance oci : output_correct_interface.
Proof using smci si lmi lacimi aemi.
split.
exact output_correct.
End OutputCorrect.

Lemma applyEntries_output_correct : forall l c i o h st os st' es, applyEntries h st l = (os, st') -> in_output_list c i o os -> (stateMachine st = snd (execute_log (deduplicate_log es))) -> (forall c i o, getLastId st c = Some (i, o) -> output_correct c i o es) -> (forall c i o e', getLastId st c = Some (i, o) -> In e' es -> eClient e' = c -> eId e' <= i) -> (forall e', In e' es -> exists i o, getLastId st (eClient e') = Some (i, o) /\ eId e' <= i) -> output_correct c i o (es ++ l).
Proof using out id client.
induction l; intros; simpl in *.
-
find_inversion.
exfalso.
eapply in_output_list_empty; eauto.
-
repeat break_let.
find_inversion.
find_apply_lem_hyp in_output_list_app_or.
break_or_hyp.
+
break_if.
*
unfold in_output_list in *.
do_in_map.
find_inversion.
rewrite middle_app_assoc.
apply output_correct_monotonic.
eapply cacheApplyEntry_output_correct; eauto.
*
exfalso.
eapply in_output_list_empty; eauto.
+
rewrite middle_app_assoc.
eapply IHl.
*
eauto.
*
auto.
*
eapply cacheApplyEntry_stateMachine_correct; eauto.
intros.
find_apply_hyp_hyp.
unfold output_correct in *.
break_exists.
break_and.
eexists.
intuition eauto.
eapply deduplicate_log_In_if.
eauto with *.
*
find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
{
intros.
break_or_hyp.
-
break_and.
apply output_correct_monotonic.
unfold getLastId in *.
repeat find_rewrite.
eauto.
-
break_let.
break_and.
unfold getLastId in *.
repeat find_rewrite.
destruct (clientId_eq_dec (eClient a) c0).
+
subst.
rewrite get_set_same in *.
find_inversion.
eapply cacheApplyEntry_output_correct; eauto.
+
rewrite get_set_diff in * by auto.
eauto using output_correct_monotonic.
}
*
intros.
do_in_app.
simpl in *.
{
intuition.
-
eapply_prop_hyp In In.
break_exists.
break_and.
subst.
eauto using le_trans, cacheAppliedEntry_clientCache_nondecreasing.
-
subst.
find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
intuition.
+
break_exists.
break_and.
eauto using le_trans, cacheAppliedEntry_clientCache_nondecreasing.
+
unfold getLastId in *.
break_let.
break_and.
repeat find_rewrite.
rewrite get_set_same in *.
find_inversion.
auto.
+
unfold getLastId in *.
break_let.
break_and.
repeat find_rewrite.
rewrite get_set_same in *.
find_inversion.
auto.
}
*
intros.
do_in_app.
simpl in *.
{
intuition.
-
eapply_prop_hyp In In.
break_exists.
break_and.
find_copy_eapply_lem_hyp cacheAppliedEntry_clientCache_preserved; eauto.
break_exists_exists.
intuition.
-
subst.
find_copy_apply_lem_hyp cacheApplyEntry_clientCache.
intuition.
+
break_exists.
break_and.
find_copy_eapply_lem_hyp cacheAppliedEntry_clientCache_preserved; eauto.
break_exists_exists.
intuition.
+
break_let.
break_and.
unfold getLastId.
repeat find_rewrite.
eexists.
eexists.
rewrite get_set_same.
intuition eauto.
+
break_let.
break_and.
unfold getLastId.
repeat find_rewrite.
eexists.
eexists.
rewrite get_set_same.
intuition eauto.
}
