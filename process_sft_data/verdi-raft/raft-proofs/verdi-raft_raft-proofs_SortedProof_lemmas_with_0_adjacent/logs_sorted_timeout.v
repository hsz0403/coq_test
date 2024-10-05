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

Theorem logs_sorted_timeout : raft_net_invariant_timeout logs_sorted.
Proof using.
unfold raft_net_invariant_timeout.
unfold logs_sorted.
intuition.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp handleTimeout_log.
find_higher_order_rewrite.
break_match; repeat find_rewrite; eauto.
-
eapply logs_sorted_nw_no_append_entries; eauto.
intros.
eauto using handleTimeout_not_is_append_entries.
-
eapply packets_gt_prevIndex_no_append_entries; eauto.
intros.
eauto using handleTimeout_not_is_append_entries.
-
eapply packets_ge_prevTerm_no_append_entries; eauto.
intros.
eauto using handleTimeout_not_is_append_entries.
