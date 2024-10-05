Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Section TermsAndIndicesFromOneLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {ctgzi : current_term_gt_zero_interface}.
Definition terms_and_indices_from_one_log_ind (net : network) : Prop := terms_and_indices_from_one_log net /\ terms_and_indices_from_one_log_nw net.
Instance taifoli : terms_and_indices_from_one_log_interface.
Proof.
split.
-
apply terms_and_indices_from_one_log_ind_invariant.
-
apply terms_and_indices_from_one_log_ind_invariant.
End TermsAndIndicesFromOneLog.

Lemma terms_and_indices_from_one_log_ind_invariant : forall net, raft_intermediate_reachable net -> terms_and_indices_from_one_log_ind net.
Proof using ctgzi.
intros.
apply raft_net_invariant; auto.
-
apply terms_and_indices_from_one_log_ind_init.
-
apply terms_and_indices_from_one_log_ind_client_request.
-
apply terms_and_indices_from_one_log_ind_timeout.
-
apply terms_and_indices_from_one_log_ind_append_entries.
-
apply terms_and_indices_from_one_log_ind_append_entries_reply.
-
apply terms_and_indices_from_one_log_ind_request_vote.
-
apply terms_and_indices_from_one_log_ind_request_vote_reply.
-
apply terms_and_indices_from_one_log_ind_do_leader.
-
apply terms_and_indices_from_one_log_ind_do_generic_server.
-
apply terms_and_indices_from_one_log_ind_state_same_packet_subset.
-
apply terms_and_indices_from_one_log_ind_reboot.
