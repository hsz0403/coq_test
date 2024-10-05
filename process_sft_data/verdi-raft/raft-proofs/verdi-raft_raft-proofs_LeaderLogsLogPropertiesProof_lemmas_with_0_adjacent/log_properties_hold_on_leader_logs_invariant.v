Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.LeaderLogsLogPropertiesInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Section LeaderLogsLogProperties.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Ltac finish := solve [eapply_prop_hyp In In; eauto].
Instance lpholli : log_properties_hold_on_leader_logs_interface.
split.
auto using log_properties_hold_on_leader_logs_invariant.
Defined.
End LeaderLogsLogProperties.

Theorem log_properties_hold_on_leader_logs_invariant : forall net, refined_raft_intermediate_reachable net -> log_properties_hold_on_leader_logs net.
Proof using rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply log_properties_hold_on_leader_logs_init.
-
apply log_properties_hold_on_leader_logs_client_request.
-
apply log_properties_hold_on_leader_logs_timeout.
-
apply log_properties_hold_on_leader_logs_append_entries.
-
apply log_properties_hold_on_leader_logs_append_entries_reply.
-
apply log_properties_hold_on_leader_logs_request_vote.
-
apply log_properties_hold_on_leader_logs_request_vote_reply.
-
apply log_properties_hold_on_leader_logs_do_leader.
-
apply log_properties_hold_on_leader_logs_do_generic_server.
-
apply log_properties_hold_on_leader_logs_state_same_packet_subset.
-
apply log_properties_hold_on_leader_logs_reboot.
