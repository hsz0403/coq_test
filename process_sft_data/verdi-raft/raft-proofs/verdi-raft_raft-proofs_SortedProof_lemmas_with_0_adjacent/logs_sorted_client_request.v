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

Theorem logs_sorted_client_request : raft_net_invariant_client_request logs_sorted.
Proof using tsi.
unfold raft_net_invariant_client_request.
unfold logs_sorted.
intuition.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_higher_order_rewrite.
break_match; eauto.
subst.
eauto using handleClientRequest_logs_sorted.
-
find_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
eauto using logs_sorted_nw_packets_unchanged.
-
find_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
eauto using packets_gt_prevIndex_packets_unchanged.
-
find_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
eauto using packets_ge_prevTerm_packets_unchanged.
