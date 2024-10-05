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

Lemma log_properties_hold_on_leader_logs_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset log_properties_hold_on_leader_logs.
Proof using.
red.
unfold log_properties_hold_on_leader_logs.
intros.
simpl in *.
subst.
repeat find_reverse_higher_order_rewrite.
finish.
