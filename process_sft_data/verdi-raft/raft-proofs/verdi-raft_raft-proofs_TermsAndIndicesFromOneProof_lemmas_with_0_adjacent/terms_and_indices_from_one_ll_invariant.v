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

Lemma terms_and_indices_from_one_ll_invariant : forall net, refined_raft_intermediate_reachable net -> terms_and_indices_from_one_ll net.
Proof using taifoli rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply terms_and_indices_from_one_ll_init.
-
apply terms_and_indices_from_one_ll_client_request.
-
apply terms_and_indices_from_one_ll_timeout.
-
apply terms_and_indices_from_one_ll_append_entries.
-
apply terms_and_indices_from_one_ll_append_entries_reply.
-
apply terms_and_indices_from_one_ll_request_vote.
-
apply terms_and_indices_from_one_ll_request_vote_reply.
-
apply terms_and_indices_from_one_ll_do_leader.
-
apply terms_and_indices_from_one_ll_do_generic_server.
-
apply terms_and_indices_from_one_ll_state_same_packet_subset.
-
apply terms_and_indices_from_one_ll_reboot.
