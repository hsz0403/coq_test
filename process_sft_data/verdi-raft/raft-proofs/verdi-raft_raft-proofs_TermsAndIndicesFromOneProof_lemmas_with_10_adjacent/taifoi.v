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

Lemma terms_and_indices_from_one_ll_timeout : refined_raft_net_invariant_timeout terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_timeout, terms_and_indices_from_one_ll.
simpl.
intuition.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_rewrite_lem update_elections_data_timeout_leaderLogs.
Admitted.

Lemma terms_and_indices_from_one_ll_append_entries : refined_raft_net_invariant_append_entries terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_append_entries, terms_and_indices_from_one_ll.
simpl.
intuition.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
Admitted.

Lemma terms_and_indices_from_one_ll_append_entries_reply : refined_raft_net_invariant_append_entries_reply terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, terms_and_indices_from_one_ll.
simpl.
intuition.
repeat find_higher_order_rewrite.
Admitted.

Lemma terms_and_indices_from_one_ll_request_vote : refined_raft_net_invariant_request_vote terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_request_vote, terms_and_indices_from_one_ll.
simpl.
intuition.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_rewrite_lem leaderLogs_update_elections_data_requestVote.
Admitted.

Lemma terms_and_indices_from_one_ll_request_vote_reply : refined_raft_net_invariant_request_vote_reply terms_and_indices_from_one_ll.
Proof using taifoli rri.
unfold refined_raft_net_invariant_request_vote_reply, terms_and_indices_from_one_ll.
simpl.
intuition.
repeat find_higher_order_rewrite.
update_destruct; rewrite_update; eauto.
simpl in *.
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto.
find_apply_lem_hyp handleRequestVoteReply_log.
intuition; eauto; subst.
find_rewrite.
Admitted.

Lemma terms_and_indices_from_one_ll_do_leader : refined_raft_net_invariant_do_leader terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_do_leader, terms_and_indices_from_one_ll.
simpl.
intuition.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
eapply H0.
find_higher_order_rewrite.
Admitted.

Lemma terms_and_indices_from_one_ll_do_generic_server : refined_raft_net_invariant_do_generic_server terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, terms_and_indices_from_one_ll.
simpl.
intuition.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
eapply H0.
find_higher_order_rewrite.
Admitted.

Lemma terms_and_indices_from_one_ll_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_state_same_packet_subset, terms_and_indices_from_one_ll.
simpl.
intuition.
find_reverse_higher_order_rewrite.
Admitted.

Lemma terms_and_indices_from_one_ll_reboot : refined_raft_net_invariant_reboot terms_and_indices_from_one_ll.
Proof using.
unfold refined_raft_net_invariant_reboot, terms_and_indices_from_one_ll.
simpl.
intuition.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
eapply H0.
find_higher_order_rewrite.
Admitted.

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
Admitted.

Instance taifoi : terms_and_indices_from_one_interface.
Proof.
constructor.
split.
-
auto using terms_and_indices_from_one_vwl_invariant.
-
auto using terms_and_indices_from_one_ll_invariant.
