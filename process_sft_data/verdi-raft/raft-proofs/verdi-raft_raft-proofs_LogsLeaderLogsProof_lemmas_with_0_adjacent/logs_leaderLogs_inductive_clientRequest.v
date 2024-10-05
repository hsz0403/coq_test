Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LeaderLogsLogPropertiesInterface.
Section LogsLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {lllmi : leaderLogs_entries_match_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {nisi : nextIndex_safety_interface}.
Context {si : sorted_interface}.
Context {lpholli : log_properties_hold_on_leader_logs_interface}.
Definition weak_sanity pli ll ll' := pli = 0 -> (exists e, eIndex e = 0 /\ In e ll) \/ ll = ll'.
Definition logs_leaderLogs_nw_weak net := forall p t n pli plt es ci e, In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In e es -> exists leader ll es' ll', In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) /\ Prefix ll' ll /\ removeAfterIndex es (eIndex e) = es' ++ ll' /\ (forall e', In e' es' -> eTerm e' = eTerm e) /\ weak_sanity pli ll ll'.
Definition logs_leaderLogs_inductive net := logs_leaderLogs net /\ logs_leaderLogs_nw net.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance llli : logs_leaderLogs_interface.
Proof.
split; eauto using logs_leaderLogs_invariant, logs_leaderLogs_nw_invariant.
End LogsLeaderLogs.

Lemma logs_leaderLogs_inductive_clientRequest : refined_raft_net_invariant_client_request logs_leaderLogs_inductive.
Proof using si lhllsi rri.
red.
unfold logs_leaderLogs_inductive.
intros.
intuition.
-
subst.
unfold logs_leaderLogs in *.
intros.
simpl in *.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *.
+
find_apply_lem_hyp handleClientRequest_log.
intuition; subst; repeat find_rewrite.
*
find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
*
{
break_exists.
intuition.
repeat find_rewrite.
simpl in *.
intuition; subst.
-
find_apply_lem_hyp leaders_have_leaderLogs_strong_invariant; eauto.
break_exists.
intuition.
unfold ghost_data in *.
simpl in *.
repeat find_rewrite.
match goal with | h : name, _ : _ = ?e :: ?es ++ ?ll |- _ => exists h, ll, (e :: x0) end; intuition.
+
find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
+
break_if; eauto using app_ass; do_bool; omega.
+
simpl in *.
intuition; subst; eauto.
-
find_copy_apply_lem_hyp maxIndex_is_max; eauto using lift_logs_sorted.
find_apply_hyp_hyp.
break_exists_exists; intuition; [find_higher_order_rewrite ; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto|].
break_if; do_bool; intuition; omega.
}
+
find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
-
unfold logs_leaderLogs_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
eapply_prop_hyp In pBody; eauto; break_exists_exists; intuition; subst; repeat find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
+
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp handleClientRequest_no_append_entries; eauto.
intuition.
find_false.
repeat find_rewrite.
repeat eexists; eauto.
