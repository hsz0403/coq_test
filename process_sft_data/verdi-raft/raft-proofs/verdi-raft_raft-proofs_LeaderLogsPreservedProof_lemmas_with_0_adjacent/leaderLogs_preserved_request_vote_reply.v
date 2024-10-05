Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderLogsPreservedInterface.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.LeaderLogsCandidateEntriesInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Section LeaderLogsPreserved.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llli : logs_leaderLogs_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {llcei : leaderLogs_candidate_entries_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Instance llpi : leaderLogs_preserved_interface.
split.
eauto using leaderLogs_preserved_invariant.
Defined.
End LeaderLogsPreserved.

Lemma leaderLogs_preserved_request_vote_reply : refined_raft_net_invariant_request_vote_reply leaderLogs_preserved.
Proof using cci vci ollpti llcei lltsi llli.
red.
unfold leaderLogs_preserved.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; repeat find_apply_lem_hyp update_elections_data_requestVoteReply_leaderLogs'; intuition; subst; eauto.
-
exfalso.
match goal with | H : In _ ?ll, _ : In (_, ?ll) _ |- _ => eapply leaderLogs_term_sanity_invariant in H end; eauto.
find_eapply_lem_hyp leaderLogs_currentTerm_invariant; eauto.
repeat find_rewrite.
repeat (unfold raft_data in *; simpl in *).
omega.
-
find_apply_lem_hyp logs_leaderLogs_invariant; auto.
break_exists.
intuition.
find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto; conclude_using eauto.
subst.
find_eapply_lem_hyp app_in_2; eauto using removeAfterIndex_in.
-
find_apply_lem_hyp logs_leaderLogs_invariant; auto.
break_exists.
intuition.
find_eapply_lem_hyp one_leaderLog_per_term_log_invariant; eauto; conclude_using eauto.
subst.
find_eapply_lem_hyp app_in_2; eauto using removeAfterIndex_in.
-
match goal with | H : In _ ?ll, _ : In (_, ?ll) _ |- _ => eapply leaderLogs_candidate_entries_invariant in H end; eauto.
find_eapply_lem_hyp wonElection_candidateEntries_rvr; repeat find_rewrite; eauto using votes_correct_invariant, cronies_correct_invariant.
intuition.
