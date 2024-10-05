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

Theorem packets_gt_prevIndex_no_append_entries : forall net ps' l st', packets_gt_prevIndex net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p l) -> (forall p, In p l -> ~ is_append_entries (pBody p)) -> packets_gt_prevIndex (mkNetwork ps' st').
Proof using.
intros.
eapply packets_gt_prevIndex_only_new_packets_matter; eauto.
unfold packets_gt_prevIndex.
intros.
simpl in *.
find_apply_hyp_hyp.
exfalso.
match goal with H : _ |- _ => apply H end.
repeat eexists; eauto.
