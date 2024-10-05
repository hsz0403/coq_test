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

Lemma match_index_all_entries_request_vote_reply : refined_raft_net_invariant_request_vote_reply match_index_all_entries_inv.
Proof using cci vci cei laei taifoli rri.
unfold refined_raft_net_invariant_request_vote_reply, match_index_all_entries_inv.
simpl.
intros.
split.
-
unfold match_index_all_entries in *.
simpl.
intros.
break_and.
find_apply_lem_hyp handleRequestVoteReply_spec.
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
+
intuition; try congruence.
*
subst.
{
update_destruct_simplify_hyp.
-
rewrite update_elections_data_requestVoteReply_allEntries.
repeat find_reverse_rewrite.
eauto.
-
repeat find_reverse_rewrite.
eauto.
}
*
repeat find_rewrite.
unfold assoc_default in *.
{
break_match.
-
simpl in *.
break_if; try discriminate.
match goal with | [ H : Some _ = Some _ |- _ ] => invc H end.
rewrite_update.
simpl.
rewrite update_elections_data_requestVoteReply_allEntries.
match goal with | [ |- In (?t, _) _ ] => replace t with (eTerm e) by congruence end.
eapply log_all_entries_invariant; auto.
-
find_apply_lem_hyp lifted_terms_and_indices_from_one_log; auto.
intuition.
omega.
}
+
update_destruct_simplify_hyp.
*
rewrite update_elections_data_requestVoteReply_allEntries.
repeat find_reverse_rewrite.
eauto.
*
repeat find_reverse_rewrite.
eauto.
-
unfold match_index_all_entries_nw in *.
simpl in *.
intros.
find_apply_lem_hyp handleRequestVoteReply_spec'.
repeat find_higher_order_rewrite.
find_apply_hyp_hyp.
update_destruct_simplify_hyp.
+
intuition; try congruence.
*
subst.
{
update_destruct_simplify_hyp.
-
rewrite update_elections_data_requestVoteReply_allEntries.
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; congruence end.
-
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; congruence end.
}
*
subst.
intro_refined_invariant candidate_entries_invariant.
match goal with | [ H : candidateEntries_host_invariant _ |- _ ] => pose proof H (pDst p) e end.
unfold raft_data in *.
conclude_using congruence.
{
find_eapply_lem_hyp wonElection_candidateEntries_rvr; eauto.
-
intuition.
-
eauto using votes_correct_invariant.
-
eauto using cronies_correct_invariant.
-
unfold raft_refined_base_params, raft_refined_multi_params in *.
congruence.
-
unfold raft_refined_multi_params, raft_refined_base_params in *.
simpl in *.
unfold raft_data in *.
congruence.
}
+
{
update_destruct_simplify_hyp.
-
rewrite update_elections_data_requestVoteReply_allEntries.
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; congruence end.
-
repeat find_rewrite.
match goal with | [ H : context [ In _ (allEntries _) ] |- _ ] => eapply H; eauto; congruence end.
}
