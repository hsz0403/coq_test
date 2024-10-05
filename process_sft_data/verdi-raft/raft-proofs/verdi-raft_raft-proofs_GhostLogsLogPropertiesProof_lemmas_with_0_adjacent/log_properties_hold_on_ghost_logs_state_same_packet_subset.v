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

Lemma log_properties_hold_on_ghost_logs_state_same_packet_subset : msg_refined_raft_net_invariant_state_same_packet_subset log_properties_hold_on_ghost_logs.
Proof using.
red.
unfold log_properties_hold_on_ghost_logs.
intros.
simpl in *.
subst.
repeat find_reverse_rewrite.
eapply_prop_hyp msg_log_property msg_log_property; eauto.
