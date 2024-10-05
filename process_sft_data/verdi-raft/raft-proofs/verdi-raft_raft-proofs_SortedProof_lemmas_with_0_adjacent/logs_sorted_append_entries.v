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

Theorem logs_sorted_append_entries : raft_net_invariant_append_entries logs_sorted.
Proof using.
unfold raft_net_invariant_append_entries.
intros.
unfold logs_sorted.
intuition.
-
unfold logs_sorted_host.
simpl in *.
intros.
repeat find_higher_order_rewrite.
break_match; repeat find_rewrite; eauto; [|unfold logs_sorted in *; intuition eauto].
subst.
eauto using handleAppendEntries_logs_sorted.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply logs_sorted_nw_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
eauto using handleAppendEntries_not_append_entries.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply packets_gt_prevIndex_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
eauto using handleAppendEntries_not_append_entries.
-
unfold logs_sorted in *.
intuition.
simpl in *.
eapply packets_ge_prevTerm_not_append_entries; eauto.
+
intros.
find_apply_hyp_hyp.
intuition eauto.
+
simpl.
eauto using handleAppendEntries_not_append_entries.
