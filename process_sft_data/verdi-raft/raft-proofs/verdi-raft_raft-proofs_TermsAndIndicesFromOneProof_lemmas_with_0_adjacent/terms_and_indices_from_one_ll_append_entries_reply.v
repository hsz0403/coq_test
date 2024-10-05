Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermsAndIndicesFromOneInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Section TermsAndIndicesFromOne.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Instance taifoi : terms_and_indices_from_one_interface.
Proof.
constructor.
split.
-
auto using terms_and_indices_from_one_vwl_invariant.
-
auto using terms_and_indices_from_one_ll_invariant.
End TermsAndIndicesFromOne.

Lemma terms_and_indices_from_one_ll_append_entries_reply : refined_raft_net_invariant_append_entries_reply terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, terms_and_indices_from_one_ll.
simpl.
intuition.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
