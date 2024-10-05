Require Import Verdi.GhostSimulations.
Require Import Verdi.InverseTraceRelations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.InputBeforeOutputInterface.
Require Import VerdiRaft.AppliedImpliesInputInterface.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Require Import VerdiRaft.LastAppliedCommitIndexMatchingInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.UniqueIndicesInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section InputBeforeOutput.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {oiai : output_implies_applied_interface}.
Context {aiii : applied_implies_input_interface}.
Context {si : sorted_interface}.
Context {lacimi : lastApplied_commitIndex_match_interface}.
Context {lmi : log_matching_interface}.
Context {smsi : state_machine_safety_interface}.
Context {misi : max_index_sanity_interface}.
Context {uii : unique_indices_interface}.
Section inner.
Variable client : clientId.
Variable id : nat.
Fixpoint client_id_in l := match l with | [] => false | e :: l' => if (andb (if clientId_eq_dec (eClient e) client then true else false) (eId e =? id)) then true else client_id_in l' end.
Program Instance TR : InverseTraceRelation step_failure := { init := step_failure_init; T := input_before_output client id; R := fun s => in_applied_entries client id (snd s) }.
Next Obligation.
destruct (client_id_in (applied_entries (nwState n))) eqn:?; eauto using client_id_in_true_in_applied_entries, client_id_in_false_not_in_applied_entries.
Defined.
Next Obligation.
unfold input_before_output in *.
eauto using before_func_app.
Defined.
Next Obligation.
intuition.
simpl in *.
unfold in_applied_entries, applied_entries in *.
simpl in *.
break_match; simpl in *; break_exists; intuition.
Defined.
Next Obligation.
simpl in *.
find_eapply_lem_hyp in_applied_entries_step_applied_implies_input_state; eauto.
break_or_hyp.
-
break_exists.
intuition.
find_eapply_lem_hyp applied_implies_input; eauto.
apply before_func_app.
destruct (key_in_output_trace_dec client id tr); [find_eapply_lem_hyp output_implies_applied; eauto; intuition|].
fold (input_before_output client id tr).
subst.
eauto using in_input_not_in_output_input_before_output.
-
destruct (key_in_output_trace_dec client id tr); [find_eapply_lem_hyp output_implies_applied; eauto; intuition|].
break_exists.
subst.
eauto using input_before_output_not_key_in_output_trace_snoc_key.
Defined.
End inner.
Instance iboi : input_before_output_interface.
Proof.
split.
intros.
eapply output_implies_input_before_output; eauto.
End InputBeforeOutput.

Lemma handleMessage_applied_entries : forall net h h' m st' ms, raft_intermediate_reachable net -> In {| pBody := m; pDst := h; pSrc := h' |} (nwPackets net) -> handleMessage h' h m (nwState net h) = (st', ms) -> applied_entries (nwState net) = applied_entries (update name_eq_dec (nwState net) h st').
Proof using uii misi smsi lmi si.
intros.
symmetry.
unfold handleMessage in *.
break_match; repeat break_let; repeat find_inversion.
-
apply applied_entries_log_lastApplied_update_same; eauto using handleRequestVote_same_log, handleRequestVote_same_lastApplied.
-
apply applied_entries_log_lastApplied_update_same; eauto using handleRequestVoteReply_same_log, handleRequestVoteReply_same_lastApplied.
-
find_copy_eapply_lem_hyp handleAppendEntries_logs_sorted; eauto using logs_sorted_invariant.
apply applied_entries_safe_update; eauto using handleAppendEntries_same_lastApplied.
find_apply_lem_hyp handleAppendEntries_log_detailed.
intuition.
+
repeat find_rewrite.
auto.
+
subst.
find_copy_apply_lem_hyp state_machine_safety_invariant.
unfold state_machine_safety in *.
intuition.
find_copy_apply_lem_hyp max_index_sanity_invariant.
intuition.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted, maxIndex_sanity in *.
intuition.
apply removeAfterIndex_same_sufficient; eauto.
*
intros.
copy_eapply_prop_hyp state_machine_safety_nw In; unfold commit_recorded in *.
simpl in *; repeat (forwards; eauto; concludes).
intuition; try omega; exfalso; find_eapply_lem_hyp findAtIndex_max_thing; eauto; try break_exists; try congruence; eauto using entries_max_thing; find_apply_lem_hyp logs_contiguous; auto; omega.
*
intros.
find_copy_apply_lem_hyp log_matching_invariant.
unfold log_matching, log_matching_hosts in *.
intuition.
match goal with | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h (eIndex e)); forward H end; copy_eapply_prop_hyp log_matching_nw AppendEntries; eauto; repeat (forwards; [intuition eauto; omega|]; concludes); intuition; [eapply le_trans; eauto|].
match goal with | H : exists _, _ |- _ => destruct H as [e'] end.
intuition.
copy_eapply_prop_hyp state_machine_safety_nw In; unfold commit_recorded in *; simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
match goal with H : _ /\ (_ \/ _) |- _ => clear H end.
intuition; try omega; [|find_copy_apply_lem_hyp UniqueIndices_invariant; unfold UniqueIndices in *; intuition; eapply rachet; [symmetry|idtac|idtac|idtac|idtac]; eauto].
exfalso.
find_eapply_lem_hyp findAtIndex_max_thing; eauto; try break_exists; try congruence; eauto using entries_max_thing.
+
repeat find_rewrite.
find_copy_apply_lem_hyp state_machine_safety_invariant.
find_copy_apply_lem_hyp max_index_sanity_invariant.
unfold state_machine_safety, maxIndex_sanity in *.
intuition.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
*
intros.
eapply entries_gt_0; intuition eauto.
*
intros.
copy_eapply_prop_hyp state_machine_safety_nw In; unfold commit_recorded in *; simpl in *; repeat (forwards; [intuition eauto; omega|]; concludes).
match goal with H : _ /\ (_ \/ _) |- _ => clear H end.
intuition; try omega; try solve [find_apply_lem_hyp logs_contiguous; auto; omega].
exfalso.
subst.
break_exists.
intuition.
find_false.
find_apply_lem_hyp maxIndex_non_empty.
break_exists.
intuition.
repeat find_rewrite.
f_equal.
find_apply_lem_hyp findAtIndex_elim.
intuition.
eapply uniqueIndices_elim_eq with (xs := log st'); eauto using sorted_uniqueIndices.
unfold state_machine_safety_nw in *.
eapply_prop_hyp commit_recorded In; intuition; eauto; try omega; try solve [find_apply_lem_hyp logs_contiguous; auto; omega].
unfold commit_recorded.
intuition.
+
repeat find_rewrite.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
*
{
intros.
do_in_app.
intuition.
-
eapply entries_gt_0; eauto.
reflexivity.
-
find_apply_lem_hyp removeAfterIndex_in.
find_apply_lem_hyp logs_contiguous; eauto.
}
*
find_apply_lem_hyp max_index_sanity_invariant.
unfold maxIndex_sanity in *.
intuition.
*
intros.
find_copy_apply_lem_hyp state_machine_safety_invariant.
unfold state_machine_safety in *.
break_and.
copy_eapply_prop_hyp state_machine_safety_nw In; eauto.
simpl in *.
intuition eauto.
forwards; eauto.
concludes.
forwards; [unfold commit_recorded in *; intuition eauto|].
concludes.
intuition; apply in_app_iff; try solve [right; eapply removeAfterIndex_le_In; eauto; omega]; exfalso.
find_eapply_lem_hyp findAtIndex_max_thing; eauto using entries_max_thing.
break_exists; congruence.
+
break_exists.
intuition.
subst.
repeat find_rewrite.
find_copy_apply_lem_hyp logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
eapply removeAfterIndex_same_sufficient'; eauto using logs_contiguous.
*
{
intros.
do_in_app.
intuition.
-
eapply entries_gt_0; eauto.
reflexivity.
-
find_apply_lem_hyp removeAfterIndex_in.
find_apply_lem_hyp logs_contiguous; eauto.
}
*
find_apply_lem_hyp max_index_sanity_invariant.
unfold maxIndex_sanity in *.
intuition.
*
{
intros.
find_copy_apply_lem_hyp state_machine_safety_invariant.
unfold state_machine_safety in *.
break_and.
copy_eapply_prop_hyp state_machine_safety_nw In; eauto.
simpl in *.
intuition eauto.
forwards; eauto.
concludes.
forwards; [unfold commit_recorded in *; intuition eauto|].
concludes.
intuition; apply in_app_iff; try solve [right; eapply removeAfterIndex_le_In; eauto; omega].
subst.
find_apply_lem_hyp maxIndex_non_empty.
break_exists.
intuition.
repeat find_rewrite.
find_apply_lem_hyp findAtIndex_elim.
intuition.
find_false.
f_equal.
eapply uniqueIndices_elim_eq with (xs := log (nwState net h)); eauto using sorted_uniqueIndices.
unfold state_machine_safety_nw in *.
eapply rachet; eauto using sorted_app, sorted_uniqueIndices.
copy_eapply_prop_hyp commit_recorded In; intuition; eauto; try omega; unfold commit_recorded; intuition.
-
exfalso.
pose proof entries_gt_pli.
eapply_prop_hyp AppendEntries AppendEntries; [|idtac|simpl; eauto|]; eauto.
omega.
-
exfalso.
pose proof entries_gt_pli.
eapply_prop_hyp AppendEntries AppendEntries; [|idtac|simpl; eauto|]; eauto.
omega.
}
-
apply applied_entries_log_lastApplied_update_same; eauto using handleAppendEntriesReply_same_log, handleAppendEntriesReply_same_lastApplied.
