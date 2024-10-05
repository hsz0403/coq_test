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

Lemma log_properties_hold_on_ghost_logs_append_entries_reply : msg_refined_raft_net_invariant_append_entries_reply' log_properties_hold_on_ghost_logs.
Proof using.
red.
unfold log_properties_hold_on_ghost_logs.
intros.
simpl in *.
subst.
find_apply_hyp_hyp; intuition; repeat find_rewrite; try solve [eapply_prop_hyp msg_log_property msg_log_property; eauto].
do_in_map.
subst.
simpl in *.
unfold add_ghost_msg, write_ghost_msg in *.
do_in_map.
subst.
simpl in *.
unfold write_ghost_log.
simpl in *.
replace d with (snd (nwState {| nwPackets := ps'; nwState := st' |} (pDst p))) by (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
eauto.
