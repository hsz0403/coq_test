Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.NoAppendEntriesToLeaderInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.LogAllEntriesInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.MatchIndexLeaderInterface.
Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.MatchIndexAllEntriesInterface.
Section MatchIndexAllEntries.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {naetli : no_append_entries_to_leader_interface}.
Context {naetsi : no_append_entries_to_self_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {laei : log_all_entries_interface}.
Context {aelli : append_entries_leaderLogs_interface}.
Context {lsi : leader_sublog_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {mili : match_index_leader_interface}.
Context {matchisi : match_index_sanity_interface}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {cei : candidate_entries_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Definition match_index_all_entries_nw (net : network) : Prop := forall p t es e, In p (nwPackets net) -> pBody p = AppendEntriesReply t es true -> currentTerm (snd (nwState net (pDst p))) = t -> In e (log (snd (nwState net (pDst p)))) -> eTerm e = t -> eIndex e <= maxIndex es -> type (snd (nwState net (pDst p))) = Leader -> In (t, e) (allEntries (fst (nwState net (pSrc p)))).
Definition match_index_all_entries_inv (net : network) : Prop := match_index_all_entries net /\ match_index_all_entries_nw net.
Instance miaei : match_index_all_entries_interface.
Proof.
constructor.
apply match_index_all_entries_invariant.
End MatchIndexAllEntries.

Lemma match_index_all_entries_client_request : refined_raft_net_invariant_client_request match_index_all_entries_inv.
Proof using aersi matchisi mili rlmli rri.
unfold refined_raft_net_invariant_client_request, match_index_all_entries_inv.
simpl.
intros.
break_and.
split.
-
unfold match_index_all_entries in *.
simpl in *.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
+
find_copy_apply_lem_hyp handleClientRequest_type.
find_copy_apply_lem_hyp handleClientRequest_matchIndex_log.
intuition.
*
repeat find_rewrite.
{
update_destruct_simplify_hyp.
-
apply update_elections_data_clientRequest_allEntries_old'.
find_apply_hyp_hyp.
repeat find_rewrite.
auto.
-
find_apply_hyp_hyp.
repeat find_rewrite.
auto.
}
*
break_exists.
break_and.
repeat find_rewrite.
{
update_destruct_simplify_hyp.
-
unfold update_elections_data_client_request.
find_rewrite.
break_if.
+
repeat find_rewrite.
simpl.
break_or_hyp.
*
auto.
*
right.
find_copy_apply_lem_hyp maxIndex_is_max; [|solve[apply entries_sorted_invariant; auto]].
rewrite <- lifted_match_index_leader in * by auto.
eapply_prop_hyp In In; eauto.
repeat find_rewrite.
auto.
+
do_bool.
find_rewrite.
simpl length in *.
omega.
-
find_erewrite_lem get_set_diff_default.
pose proof lifted_match_index_sanity _ leader h0 ltac:(eauto) ltac:(auto).
break_or_hyp.
+
simpl in *.
omega.
+
find_apply_hyp_hyp.
repeat find_rewrite.
auto.
}
+
find_apply_hyp_hyp.
update_destruct_simplify_hyp.
*
apply update_elections_data_clientRequest_allEntries_old'.
repeat find_rewrite.
auto.
*
repeat find_rewrite.
auto.
-
unfold match_index_all_entries_nw in *.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
+
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
*
find_copy_apply_lem_hyp handleClientRequest_type.
break_and.
repeat find_rewrite.
find_copy_apply_lem_hyp handleClientRequest_log.
{
intuition.
-
repeat find_rewrite.
eapply_prop_hyp In In; eauto.
update_destruct_simplify_hyp.
+
apply update_elections_data_clientRequest_allEntries_old'.
repeat find_rewrite.
auto.
+
repeat find_rewrite.
auto.
-
break_exists.
break_and.
repeat find_rewrite.
assert (es <> nil).
{
apply maxIndex_gt_0_nonempty.
eapply lt_le_trans; [|eauto].
simpl in *.
break_or_hyp.
-
repeat find_rewrite.
omega.
-
eapply entries_gt_0_invariant; eauto.
}
pose proof maxIndex_non_empty es.
concludes.
break_exists_name max_e.
intuition.
find_eapply_lem_hyp lifted_append_entries_reply_sublog; repeat find_rewrite; eauto.
simpl In in *.
break_or_hyp.
+
find_apply_lem_hyp maxIndex_is_max; [|solve[apply entries_sorted_invariant; auto]].
omega.
+
eapply_prop_hyp In In; eauto; [|solve[repeat find_rewrite; auto]].
update_destruct_simplify_hyp.
*
apply update_elections_data_clientRequest_allEntries_old'.
repeat find_rewrite.
auto.
*
repeat find_rewrite.
auto.
}
*
eapply_prop_hyp In In; eauto.
{
update_destruct_simplify_hyp.
-
apply update_elections_data_clientRequest_allEntries_old'.
repeat find_rewrite.
auto.
-
repeat find_rewrite.
auto.
}
+
find_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
intuition.
