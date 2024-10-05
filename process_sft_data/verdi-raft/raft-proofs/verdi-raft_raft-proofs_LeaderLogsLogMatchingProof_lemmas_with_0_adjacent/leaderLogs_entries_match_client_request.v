Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LeaderLogsSublogInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Section LeaderLogsLogMatching.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lmi : log_matching_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {si : sorted_interface}.
Context {llsli : leaderLogs_sublog_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {taifoi : terms_and_indices_from_one_interface}.
Definition leaderLogs_entries_match_nw (net : network) : Prop := forall h llt ll p t src pli plt es ci, In (llt, ll) (leaderLogs (fst (nwState net h))) -> In p (nwPackets net) -> pBody p = AppendEntries t src pli plt es ci -> (forall e1 e2, eIndex e1 = eIndex e2 -> eTerm e1 = eTerm e2 -> In e1 es -> In e2 ll -> (forall e3, eIndex e3 <= eIndex e1 -> In e3 es -> In e3 ll) /\ (pli <> 0 -> exists e4, eIndex e4 = pli /\ eTerm e4 = plt /\ In e4 ll)).
Definition leaderLogs_entries_match (net : network) : Prop := leaderLogs_entries_match_host net /\ leaderLogs_entries_match_nw net.
Ltac use_log_matching_nw := pose proof (lifted_log_matching_nw _ ltac:(eauto)); match goal with | [ H : _ |- _ ] => eapply H; [|eauto]; repeat find_rewrite; intuition end.
Instance lllmi : leaderLogs_entries_match_interface : Prop.
Proof.
split.
apply leaderLogs_entries_match_invariant.
End LeaderLogsLogMatching.

Lemma leaderLogs_entries_match_client_request : refined_raft_net_invariant_client_request leaderLogs_entries_match.
Proof using llsli si llsi lltsi rri.
unfold refined_raft_net_invariant_client_request, leaderLogs_entries_match.
intros.
split.
-
{
unfold leaderLogs_entries_match_host.
simpl.
intuition.
subst.
repeat find_higher_order_rewrite.
repeat update_destruct_simplify.
-
find_rewrite_lem update_elections_data_client_request_leaderLogs.
destruct (log d) using (handleClientRequest_log_ind ltac:(eauto)).
+
eauto.
+
destruct ll.
*
apply entries_match_nil.
*
{
apply entries_match_cons_gt_maxTerm; eauto.
-
eauto using lifted_logs_sorted_host.
-
eapply leaderLogs_sorted_invariant; eauto.
-
omega.
-
find_copy_apply_lem_hyp leaderLogs_currentTerm_invariant; auto.
find_copy_apply_lem_hyp leaderLogs_term_sanity_invariant.
unfold leaderLogs_term_sanity in *.
eapply_prop_hyp In In; simpl; eauto.
repeat find_rewrite.
simpl in *.
omega.
}
-
destruct (log d) using (handleClientRequest_log_ind ltac:(eauto)).
+
eauto.
+
apply entries_match_cons_sublog; eauto.
*
eauto using lifted_logs_sorted_host.
*
eapply leaderLogs_sorted_invariant; eauto.
*
omega.
*
intros.
eapply leaderLogs_sublog_invariant; eauto.
simpl in *.
congruence.
-
find_rewrite_lem update_elections_data_client_request_leaderLogs.
eauto.
-
eauto.
}
-
eapply leaderLogs_entries_match_nw_packet_set with (net:=net); intuition.
+
find_apply_hyp_hyp.
intuition eauto.
erewrite handleClientRequest_no_send with (ms := l) in * by eauto.
simpl in *.
intuition.
+
simpl.
subst.
find_higher_order_rewrite.
rewrite update_fun_comm.
simpl.
rewrite update_fun_comm.
simpl.
rewrite update_elections_data_client_request_leaderLogs.
now rewrite update_nop_ext' by auto.
