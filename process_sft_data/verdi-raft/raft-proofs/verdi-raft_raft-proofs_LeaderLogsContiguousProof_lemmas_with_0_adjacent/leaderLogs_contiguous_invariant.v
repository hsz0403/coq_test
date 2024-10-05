Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.LogMatchingInterface.
Section LeaderLogsContiguous.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lmi : log_matching_interface}.
Ltac start := red; unfold leaderLogs_contiguous; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Instance llci : leaderLogs_contiguous_interface : Prop.
Proof.
split.
exact leaderLogs_contiguous_invariant.
End LeaderLogsContiguous.

Lemma leaderLogs_contiguous_invariant : forall net, refined_raft_intermediate_reachable net -> leaderLogs_contiguous net.
Proof using lmi rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply leaderLogs_contiguous_init.
-
apply leaderLogs_contiguous_client_request.
-
apply leaderLogs_contiguous_timeout.
-
apply leaderLogs_contiguous_append_entries.
-
apply leaderLogs_contiguous_append_entries_reply.
-
apply leaderLogs_contiguous_request_vote.
-
apply leaderLogs_contiguous_request_vote_reply.
-
apply leaderLogs_contiguous_do_leader.
-
apply leaderLogs_contiguous_do_generic_server.
-
apply leaderLogs_contiguous_state_same_packet_subset.
-
apply leaderLogs_contiguous_reboot.
