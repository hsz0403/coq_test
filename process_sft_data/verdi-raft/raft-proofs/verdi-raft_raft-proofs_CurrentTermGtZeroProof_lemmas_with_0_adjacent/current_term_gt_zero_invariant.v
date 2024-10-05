Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Section CurrentTermGtZero.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance ctgzi : current_term_gt_zero_interface.
Proof.
split.
apply current_term_gt_zero_invariant.
End CurrentTermGtZero.

Lemma current_term_gt_zero_invariant : forall net, raft_intermediate_reachable net -> current_term_gt_zero net.
Proof using.
intros.
apply raft_net_invariant; auto.
-
apply current_term_gt_zero_init.
-
apply current_term_gt_zero_client_request.
-
apply current_term_gt_zero_timeout.
-
apply current_term_gt_zero_append_entries.
-
apply current_term_gt_zero_append_entries_reply.
-
apply current_term_gt_zero_request_vote.
-
apply current_term_gt_zero_request_vote_reply.
-
apply current_term_gt_zero_do_leader.
-
apply current_term_gt_zero_do_generic_server.
-
apply current_term_gt_zero_state_same_packet_subset.
-
apply current_term_gt_zero_reboot.
