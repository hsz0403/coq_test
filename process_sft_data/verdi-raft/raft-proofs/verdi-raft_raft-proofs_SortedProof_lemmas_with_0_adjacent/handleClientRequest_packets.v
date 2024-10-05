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

Theorem handleClientRequest_packets : forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> ps = [].
Proof using.
intros.
find_apply_lem_hyp handleClientRequest_log.
intuition.
