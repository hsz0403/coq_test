Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.VotesReceivedMoreUpToDateInterface.
Require Import VerdiRaft.RequestVoteReplyMoreUpToDateInterface.
Require Import VerdiRaft.LeaderLogsVotesWithLogInterface.
Section LeaderLogsVotesWithLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vrmutdi : votesReceived_moreUpToDate_interface}.
Context {rvrmutdi : requestVoteReply_moreUpToDate_interface}.
Instance llvwli : leaderLogs_votesWithLog_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply leaderLogs_votesWithLog_init.
-
apply leaderLogs_votesWithLog_client_request.
-
apply leaderLogs_votesWithLog_timeout.
-
apply leaderLogs_votesWithLog_append_entries.
-
apply leaderLogs_votesWithLog_append_entries_reply.
-
apply leaderLogs_votesWithLog_request_vote.
-
apply leaderLogs_votesWithLog_request_vote_reply.
-
apply leaderLogs_votesWithLog_do_leader.
-
apply leaderLogs_votesWithLog_do_generic_server.
-
apply leaderLogs_votesWithLog_state_same_packet_subset.
-
apply leaderLogs_votesWithLog_reboot.
End LeaderLogsVotesWithLog.

Lemma leaderLogs_votesWithLog_request_vote : refined_raft_net_invariant_request_vote leaderLogs_votesWithLog.
Proof using.
red.
unfold leaderLogs_votesWithLog.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
-
find_rewrite_lem leaderLogs_update_elections_data_requestVote.
eapply quorum_preserved; [|eauto].
intros.
find_higher_order_rewrite; destruct_update; simpl in *; eauto using update_elections_data_request_vote_votesWithLog_old.
-
eapply quorum_preserved; [|eauto].
intros.
find_higher_order_rewrite; destruct_update; simpl in *; eauto using update_elections_data_request_vote_votesWithLog_old.
