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

Lemma leaderLogs_entries_match_append_entries : refined_raft_net_invariant_append_entries leaderLogs_entries_match.
Proof using taifoi si llsi lmi rri.
unfold refined_raft_net_invariant_append_entries, leaderLogs_entries_match.
intuition.
-
unfold leaderLogs_entries_match_host in *.
intros.
{
intros.
simpl in *.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
find_rewrite_lem update_fun_comm.
find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
find_erewrite_lem update_nop_ext'.
update_destruct_simplify; rewrite_update; try rewrite update_elections_data_appendEntries_leaderLogs in *; eauto.
destruct (log d) using (handleAppendEntries_log_ind ltac:(eauto)); eauto.
+
subst.
eapply entries_match_scratch with (plt0 := plt).
*
eauto using lifted_logs_sorted_nw.
*
apply sorted_uniqueIndices.
eapply leaderLogs_sorted_invariant; eauto.
*
eapply_prop leaderLogs_entries_match_nw; eauto.
*
use_log_matching_nw.
*
use_log_matching_nw.
*
match goal with | [ H : In _ (leaderLogs _) |- _ ] => eapply terms_and_indices_from_one_invariant in H; [|solve[auto]] end.
unfold terms_and_indices_from_one in *.
intros.
find_apply_hyp_hyp.
intuition.
+
eapply entries_match_append; eauto.
*
eauto using lifted_logs_sorted_host.
*
eapply leaderLogs_sorted_invariant; eauto.
*
eauto using lifted_logs_sorted_nw.
*
use_log_matching_nw.
*
use_log_matching_nw.
*
eapply findAtIndex_intro; eauto using lifted_logs_sorted_host, sorted_uniqueIndices.
}
-
unfold leaderLogs_entries_match_nw in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
find_rewrite_lem update_fun_comm.
find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
find_erewrite_lem update_nop_ext'.
find_apply_hyp_hyp.
break_or_hyp.
+
intuition; match goal with | [ H : _ |- _ ] => solve [eapply H with (p0 := p0); eauto with *] end.
+
simpl in *.
find_copy_apply_lem_hyp handleAppendEntries_doesn't_send_AE.
exfalso.
eauto 10.
