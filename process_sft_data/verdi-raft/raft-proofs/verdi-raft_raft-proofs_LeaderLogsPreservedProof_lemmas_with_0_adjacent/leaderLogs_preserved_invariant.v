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

Theorem leaderLogs_preserved_invariant : forall net, refined_raft_intermediate_reachable net -> leaderLogs_preserved net.
Proof using cci vci ollpti llcei lltsi llli rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply leaderLogs_preserved_init.
-
apply leaderLogs_preserved_client_request.
-
apply leaderLogs_preserved_timeout.
-
apply leaderLogs_preserved_append_entries.
-
apply leaderLogs_preserved_append_entries_reply.
-
apply leaderLogs_preserved_request_vote.
-
apply leaderLogs_preserved_request_vote_reply.
-
apply leaderLogs_preserved_do_leader.
-
apply leaderLogs_preserved_do_generic_server.
-
apply leaderLogs_preserved_state_same_packet_subset.
-
apply leaderLogs_preserved_reboot.
