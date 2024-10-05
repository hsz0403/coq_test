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

Theorem logs_sorted_do_leader : raft_net_invariant_do_leader logs_sorted.
Proof using.
unfold raft_net_invariant_do_leader.
unfold logs_sorted.
intuition; simpl in *.
-
unfold logs_sorted_host in *.
simpl in *.
intros.
find_apply_lem_hyp doLeader_log.
repeat find_higher_order_rewrite.
break_match; subst; try find_rewrite; eauto.
-
unfold logs_sorted_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_messages; intuition; eauto using sorted_subseq.
-
unfold packets_gt_prevIndex.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_messages; [idtac|idtac|idtac|eauto]; intuition eauto.
-
unfold packets_ge_prevTerm.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_messages; [idtac|idtac|idtac|eauto]; intuition eauto.
