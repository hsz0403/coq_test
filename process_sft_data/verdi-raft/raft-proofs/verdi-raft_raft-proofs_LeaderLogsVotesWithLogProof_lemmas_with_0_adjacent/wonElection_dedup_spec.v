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

Lemma wonElection_dedup_spec : forall l, wonElection (dedup name_eq_dec l) = true -> exists quorum, NoDup quorum /\ length quorum > div2 (length nodes) /\ (forall h, In h quorum -> In h l).
Proof using.
intros.
exists (dedup name_eq_dec l).
intuition; eauto using NoDup_dedup, in_dedup_was_in.
unfold wonElection in *.
do_bool.
omega.
