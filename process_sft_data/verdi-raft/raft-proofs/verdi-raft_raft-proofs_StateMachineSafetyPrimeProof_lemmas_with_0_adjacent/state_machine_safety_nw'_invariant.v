Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.StateMachineSafetyPrimeInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.AllEntriesLeaderLogsInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.UniqueIndicesInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Section StateMachineSafety'.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lci : leader_completeness_interface}.
Context {aelli : all_entries_leader_logs_interface}.
Context {lmi : log_matching_interface}.
Context {uii : unique_indices_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {lsi : sorted_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {lllmi : leaderLogs_entries_match_interface}.
Context {llli : logs_leaderLogs_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Ltac copy_eapply_prop_hyp P Q := match goal with | [ H : context [ P ], H' : context [ Q ] |- _ ] => copy_eapply H H' end.
Ltac get_invariant i := match goal with | H : refined_raft_intermediate_reachable _ |- _ => copy_apply i H end.
Set Bullet Behavior "Strict Subproofs".
Instance sms'i : state_machine_safety'interface.
Proof.
split.
intuition.
split.
-
auto using state_machine_safety_host'_invariant.
-
auto using state_machine_safety_nw'_invariant.
End StateMachineSafety'.

Theorem state_machine_safety_nw'_invariant : forall net, refined_raft_intermediate_reachable net -> state_machine_safety_nw' net.
Proof using rlmli ollpti llli lllmi llci lsi llsi aerlli uii lmi lci rri.
unfold state_machine_safety_nw'.
intros.
unfold committed in *.
break_exists; intuition.
destruct (lt_eq_lt_dec (eTerm x0) t); intuition.
-
find_copy_apply_lem_hyp append_entries_leaderLogs_invariant.
copy_eapply_prop_hyp append_entries_leaderLogs AppendEntries; eauto.
break_exists; break_and.
get_invariant leader_completeness_invariant.
get_invariant leaderLogs_sorted_invariant.
unfold leaderLogs_sorted in *.
unfold leader_completeness in *.
break_and.
eapply_prop_hyp leader_completeness_directly_committed directly_committed; eauto.
repeat conclude_using eauto.
get_invariant leaderLogs_entries_match_invariant.
unfold leaderLogs_entries_match_host in *.
match goal with | _ : In _ (log (snd (nwState _ ?x))), H : In _ (leaderLogs _), H' : context [ entries_match ] |- _ => let H'' := fresh "H" in pose proof H as H''; eapply H' with (h := x) in H'' end.
match goal with | [ _ : In ?e ?l, _ : In ?e' ?l, _ : In ?e' ?l', H : entries_match _ _ |- _ ] => specialize(H e' e' e) end; repeat concludes.
match goal with | _ : ?P <-> ?Q, _ : ?P |- _ => assert Q by intuition end.
intuition.
+
left.
eapply gt_le_trans; eauto.
eapply maxIndex_is_max; eauto.
+
break_exists.
intuition.
subst.
match goal with | |- context [eIndex ?x > eIndex ?e ] => destruct (Compare_dec.lt_eq_lt_dec (eIndex x) (eIndex e)) end; intuition.
*
right.
right.
right.
apply in_app_iff.
right.
eapply prefix_contiguous; eauto.
{
unfold Prefix_sane in *.
intuition.
find_apply_lem_hyp (@maxIndex_is_max _ _ x2 e); eauto.
omega.
}
pose proof H1 as Happ.
find_copy_eapply_lem_hyp entries_contiguous; eauto.
eapply contiguous_app; eauto.
eapply entries_sorted_nw_invariant; eauto.
*
cut (e = x5); [intros; subst; intuition|].
eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices.
+
subst.
right.
right.
right.
apply in_app_iff.
right.
get_invariant leaderLogs_contiguous_invariant.
unfold leaderLogs_contiguous in *.
find_copy_apply_hyp_hyp.
eapply prefix_contiguous with (i := 0); eauto; [solve[eauto using in_not_nil]|match goal with | _ : In (_, ?l) (leaderLogs _), H : contiguous_range_exact_lo ?l _ |- _ => unfold contiguous_range_exact_lo in H; intuition end].
-
subst.
find_copy_eapply_lem_hyp logs_leaderLogs_invariant; eauto.
find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
break_exists.
simpl in *.
intuition.
+
subst.
match goal with | _ : In (_, ?l) (leaderLogs _), _ : In (_, ?l') (leaderLogs _) |- _ => assert (l = l') by (eapply one_leaderLog_per_term_log_invariant; eauto) end.
subst.
match goal with | _ : removeAfterIndex _ _ = ?l1 ++ ?l2 |- _ => rename l1 into new_entries; rename l2 into old_entries end.
match goal with | |- context [?l1 ++ ?l2] => rename l1 into new_msg_entries; rename l2 into old_msg_entries end.
assert (In e (new_entries ++ old_entries)) by (find_reverse_rewrite; eauto using removeAfterIndex_le_In).
do_in_app.
intuition.
*
destruct (lt_eq_lt_dec prevLogIndex (eIndex e)); intuition; try solve [subst; find_apply_hyp_hyp; intuition].
destruct (le_gt_dec (eIndex e) (maxIndex (new_msg_entries ++ old_msg_entries))); intuition.
right.
right.
right.
match goal with | |- In _ ?l => assert (contiguous_range_exact_lo l prevLogIndex) by eauto using entries_contiguous end.
unfold contiguous_range_exact_lo in *.
intuition.
match goal with | H : forall _, _ < _ <= _ -> exists _, _ |- _ => specialize (H (eIndex e)); intuition end.
break_exists.
intuition.
match goal with | _ : eIndex ?x = eIndex e |- _ => rename x into e' end.
cut (eTerm e' = eTerm e); eauto using network_host_entries.
do_in_app.
intuition; [repeat find_apply_hyp_hyp; repeat find_rewrite; auto|].
exfalso.
cut (eIndex e' < eIndex e); [intros; omega|].
match goal with | _ : In e ?ll1, _ : In e' ?ll2, _ : Prefix ?ll2 ?ll2' |- _ => apply sorted_app_in_gt with (l1 := ll1) (l2 := ll2') (e := e) (e' := e') end; eauto using Prefix_In.
repeat find_reverse_rewrite.
eauto using lift_logs_sorted, removeAfterIndex_sorted.
*
left.
find_apply_lem_hyp maxIndex_is_max; [omega|].
find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
+
break_exists.
intuition.
subst.
match goal with | _ : In (_, ?l) (leaderLogs _), _ : In (_, ?l') (leaderLogs _) |- _ => assert (l = l') by (eapply one_leaderLog_per_term_log_invariant; eauto) end.
subst.
match goal with | _ : removeAfterIndex _ _ = ?l1 ++ ?l2 |- _ => rename l1 into new_entries; rename l2 into old_entries end.
match goal with | |- context [?l1 ++ ?l2] => rename l1 into new_msg_entries; rename l2 into old_msg_entries end.
assert (In e (new_entries ++ old_entries)) by (find_reverse_rewrite; eauto using removeAfterIndex_le_In).
match goal with | _ : In ?x old_entries |- _ => rename x into base_entry end.
do_in_app.
intuition.
*
assert (eIndex base_entry < eIndex e) by (eapply sorted_app_in_gt; eauto; find_reverse_rewrite; eauto using removeAfterIndex_sorted, lift_logs_sorted).
destruct (le_gt_dec (eIndex e) (maxIndex (new_msg_entries ++ old_msg_entries))); intuition.
right.
right.
right.
match goal with | |- In _ ?l => assert (contiguous_range_exact_lo l (eIndex base_entry)) by eauto using entries_contiguous end.
unfold contiguous_range_exact_lo in *.
intuition.
match goal with | H : forall _, _ < _ <= _ -> exists _, _ |- _ => specialize (H (eIndex e)); intuition end.
break_exists.
intuition.
match goal with | _ : eIndex ?x = eIndex e |- _ => rename x into e' end.
cut (eTerm e' = eTerm e); eauto using network_host_entries.
do_in_app.
intuition; [repeat find_apply_hyp_hyp; repeat find_rewrite; auto|].
exfalso.
cut (eIndex e' < eIndex e); [intros; omega|].
match goal with | _ : In e ?ll1, _ : In e' ?ll2, _ : Prefix ?ll2 ?ll2' |- _ => apply sorted_app_in_gt with (l1 := ll1) (l2 := ll2') (e := e) (e' := e') end; eauto using Prefix_In.
repeat find_reverse_rewrite.
eauto using lift_logs_sorted, removeAfterIndex_sorted.
*
destruct (lt_eq_lt_dec (eIndex base_entry) (eIndex e)); intuition; [|cut (base_entry = e); intros; subst; intuition; eapply uniqueIndices_elim_eq; eauto; find_eapply_lem_hyp leaderLogs_sorted_invariant; eauto using sorted_uniqueIndices].
right.
right.
right.
apply in_app_iff; right.
get_invariant leaderLogs_contiguous_invariant.
unfold leaderLogs_contiguous in *.
find_copy_apply_hyp_hyp.
get_invariant leaderLogs_sorted_invariant.
unfold leaderLogs_sorted in *.
find_copy_apply_hyp_hyp.
eapply prefix_contiguous with (i := (eIndex base_entry)); eauto; [|].
{
unfold Prefix_sane in *.
intuition.
find_apply_lem_hyp (@maxIndex_is_max _ _ old_entries e); eauto.
omega.
}
find_copy_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
eauto using contiguous_app, entries_contiguous.
+
subst.
match goal with | _ : In (_, ?l) (leaderLogs _), _ : In (_, ?l') (leaderLogs _) |- _ => assert (l = l') by (eapply one_leaderLog_per_term_log_invariant; eauto) end.
subst.
match goal with | _ : removeAfterIndex _ _ = ?l1 ++ ?l2 |- _ => rename l1 into new_entries; rename l2 into old_entries end.
match goal with | |- context [?l1 ++ ?l2] => rename l1 into new_msg_entries; rename l2 into old_msg_entries end.
assert (In e (new_entries ++ old_msg_entries)) by (find_reverse_rewrite; eauto using removeAfterIndex_le_In).
assert (eIndex e > 0) by (repeat find_reverse_rewrite; find_apply_lem_hyp removeAfterIndex_in; get_invariant lift_log_matching; unfold log_matching, log_matching_hosts in *; intuition; unfold deghost in *; simpl in *; break_match; simpl in *; match goal with | H : forall _ _, In _ _ -> _ |- _ => eapply H end; eauto).
assert (0 < eIndex e) by omega.
do_in_app.
intuition.
destruct (le_gt_dec (eIndex e) (maxIndex (new_msg_entries ++ old_msg_entries))); intuition.
right.
right.
right.
match goal with | |- In _ ?l => assert (contiguous_range_exact_lo l 0) by eauto using entries_contiguous end.
unfold contiguous_range_exact_lo in *.
intuition.
match goal with | H : forall _, _ < _ <= _ -> exists _, _ |- _ => specialize (H (eIndex e)); intuition end.
break_exists.
intuition.
match goal with | _ : eIndex ?x = eIndex e |- _ => rename x into e' end.
cut (eTerm e' = eTerm e); eauto using network_host_entries.
do_in_app.
intuition; [repeat find_apply_hyp_hyp; repeat find_rewrite; auto|].
exfalso.
cut (eIndex e' < eIndex e); [intros; omega|].
match goal with | _ : In e ?ll1, _ : In e' ?ll2, _ : Prefix ?ll2 ?ll2' |- _ => apply sorted_app_in_gt with (l1 := ll1) (l2 := ll2') (e := e) (e' := e') end; eauto using Prefix_In.
repeat find_reverse_rewrite.
eauto using lift_logs_sorted, removeAfterIndex_sorted.
