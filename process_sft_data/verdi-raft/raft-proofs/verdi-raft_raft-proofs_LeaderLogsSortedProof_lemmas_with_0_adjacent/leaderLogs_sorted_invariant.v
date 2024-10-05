Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.SortedInterface.
Section LeaderLogsSorted.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance llsi : leaderLogs_sorted_interface.
Proof.
split.
eauto using leaderLogs_sorted_invariant.
Defined.
End LeaderLogsSorted.

Lemma leaderLogs_sorted_invariant : forall net, refined_raft_intermediate_reachable net -> leaderLogs_sorted net.
Proof using si rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply leaderLogs_sorted_init.
-
apply leaderLogs_sorted_client_request.
-
apply leaderLogs_sorted_timeout.
-
apply leaderLogs_sorted_append_entries.
-
apply leaderLogs_sorted_append_entries_reply.
-
apply leaderLogs_sorted_request_vote.
-
apply leaderLogs_sorted_request_vote_reply.
-
apply leaderLogs_sorted_do_leader.
-
apply leaderLogs_sorted_do_generic_server.
-
apply leaderLogs_sorted_state_same_packet_subset.
-
apply leaderLogs_sorted_reboot.
