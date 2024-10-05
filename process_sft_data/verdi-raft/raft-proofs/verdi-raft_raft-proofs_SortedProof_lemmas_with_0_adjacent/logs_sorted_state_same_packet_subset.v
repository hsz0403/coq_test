Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.SortedInterface.
Section SortedProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {tsi : term_sanity_interface}.
Ltac find_eapply_hyp_goal := match goal with | H : _ |- _ => eapply H end.
Instance si : sorted_interface.
Proof.
split.
eauto using handleAppendEntries_logs_sorted.
eauto using handleClientRequest_logs_sorted.
auto using logs_sorted_invariant.
End SortedProof.

Theorem logs_sorted_state_same_packet_subset : raft_net_invariant_state_same_packet_subset logs_sorted.
Proof using.
unfold raft_net_invariant_state_same_packet_subset, logs_sorted.
intuition; simpl in *.
-
unfold logs_sorted_host in *.
intros.
find_reverse_higher_order_rewrite.
eauto.
-
eapply logs_sorted_nw_packets_unchanged with (st' := (nwState net')); eauto.
-
eapply packets_gt_prevIndex_packets_unchanged with (st' := (nwState net')); eauto.
-
eapply packets_ge_prevTerm_packets_unchanged with (st' := (nwState net')); eauto.
