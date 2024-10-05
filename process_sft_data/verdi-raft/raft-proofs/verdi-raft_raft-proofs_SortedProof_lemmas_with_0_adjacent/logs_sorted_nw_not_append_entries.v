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

Theorem logs_sorted_nw_not_append_entries : forall net ps' p' st', logs_sorted_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ p = p') -> ~ is_append_entries (pBody p') -> logs_sorted_nw (mkNetwork ps' st').
Proof using.
intros.
unfold logs_sorted_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
-
unfold logs_sorted_nw in *.
eauto.
-
subst.
exfalso.
match goal with H : _ |- _ => apply H end.
repeat eexists; eauto.
