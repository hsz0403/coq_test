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

Theorem sorted_append : forall l l', sorted l -> sorted l' -> (forall e e', In e l -> In e' l' -> eIndex e > eIndex e') -> (forall e e', In e l -> In e' l' -> eTerm e >= eTerm e') -> sorted (l ++ l').
Proof using.
induction l; intros; simpl in *; auto.
intuition; do_in_app; intuition; find_apply_hyp_hyp; intuition.
