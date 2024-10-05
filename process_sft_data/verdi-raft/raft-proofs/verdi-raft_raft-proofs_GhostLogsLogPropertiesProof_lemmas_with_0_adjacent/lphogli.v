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

Instance lphogli : log_properties_hold_on_ghost_logs_interface.
split.
auto using log_properties_hold_on_ghost_logs_invariant.
