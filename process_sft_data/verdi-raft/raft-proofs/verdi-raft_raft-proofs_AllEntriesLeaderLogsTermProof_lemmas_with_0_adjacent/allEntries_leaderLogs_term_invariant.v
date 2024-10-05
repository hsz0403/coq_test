Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AllEntriesLeaderLogsTermInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Section AllEntriesLeaderLogsTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Instance aellti : allEntries_leaderLogs_term_interface.
split.
exact allEntries_leaderLogs_term_invariant.
End AllEntriesLeaderLogsTerm.

Lemma allEntries_leaderLogs_term_invariant : forall net, refined_raft_intermediate_reachable net -> allEntries_leaderLogs_term net.
Proof using aerlli rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply allEntries_leaderLogs_term_init.
-
apply allEntries_leaderLogs_term_client_request.
-
apply allEntries_leaderLogs_term_timeout.
-
apply allEntries_leaderLogs_term_append_entries.
-
apply allEntries_leaderLogs_term_append_entries_reply.
-
apply allEntries_leaderLogs_term_request_vote.
-
apply allEntries_leaderLogs_term_request_vote_reply.
-
apply allEntries_leaderLogs_term_do_leader.
-
apply allEntries_leaderLogs_term_do_generic_server.
-
apply allEntries_leaderLogs_term_state_same_packet_subset.
-
apply allEntries_leaderLogs_term_reboot.
