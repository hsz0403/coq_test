Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftMsgRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.GhostLogsLogPropertiesInterface.
Section GhostLogsLogProperties.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rmri : raft_msg_refinement_interface}.
Instance lphogli : log_properties_hold_on_ghost_logs_interface.
split.
auto using log_properties_hold_on_ghost_logs_invariant.
Defined.
End GhostLogsLogProperties.

Theorem log_properties_hold_on_ghost_logs_invariant : forall net, msg_refined_raft_intermediate_reachable net -> log_properties_hold_on_ghost_logs net.
Proof using rmri.
intros.
apply msg_refined_raft_net_invariant'; auto.
-
apply log_properties_hold_on_ghost_logs_init.
-
apply log_properties_hold_on_ghost_logs_client_request.
-
apply log_properties_hold_on_ghost_logs_timeout.
-
apply log_properties_hold_on_ghost_logs_append_entries.
-
apply log_properties_hold_on_ghost_logs_append_entries_reply.
-
apply log_properties_hold_on_ghost_logs_request_vote.
-
apply msg_refined_raft_net_invariant_request_vote_reply'_weak.
apply log_properties_hold_on_ghost_logs_request_vote_reply.
-
apply log_properties_hold_on_ghost_logs_do_leader.
-
apply log_properties_hold_on_ghost_logs_do_generic_server.
-
apply msg_refined_raft_net_invariant_subset'_weak.
apply log_properties_hold_on_ghost_logs_state_same_packet_subset.
-
apply msg_refined_raft_net_invariant_reboot'_weak.
apply log_properties_hold_on_ghost_logs_reboot.
