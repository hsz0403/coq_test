Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RequestVoteTermSanityInterface.
Require Import VerdiRaft.RequestVoteReplyTermSanityInterface.
Section RequestVoteReplyTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {rvtsi : requestVote_term_sanity_interface}.
Instance rvrtsi : requestVoteReply_term_sanity_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply requestVoteReply_term_sanity_init.
-
apply requestVoteReply_term_sanity_client_request.
-
apply requestVoteReply_term_sanity_timeout.
-
apply requestVoteReply_term_sanity_append_entries.
-
apply requestVoteReply_term_sanity_append_entries_reply.
-
apply requestVoteReply_term_sanity_request_vote.
-
apply requestVoteReply_term_sanity_request_vote_reply.
-
apply requestVoteReply_term_sanity_do_leader.
-
apply requestVoteReply_term_sanity_do_generic_server.
-
apply requestVoteReply_term_sanity_state_same_packet_subset.
-
apply requestVoteReply_term_sanity_reboot.
End RequestVoteReplyTermSanity.

Lemma requestVoteReply_term_sanity_request_vote : refined_raft_net_invariant_request_vote requestVoteReply_term_sanity.
Proof using rvtsi.
red.
unfold requestVoteReply_term_sanity.
intros.
simpl in *.
find_copy_apply_lem_hyp handleRequestVote_votesReceived.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
-
repeat find_rewrite.
find_apply_hyp_hyp.
intuition.
+
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
find_copy_apply_lem_hyp handleRequestVote_currentTerm_leaderId.
intuition; repeat find_rewrite; eauto; eapply_prop_hyp pBody pBody; eauto; omega.
+
remember (pDst p0).
subst p0.
simpl in *.
subst.
find_copy_apply_lem_hyp handleRequestVote_reply_true'.
intuition.
-
find_apply_hyp_hyp.
intuition.
+
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
find_copy_apply_lem_hyp handleRequestVote_currentTerm_leaderId.
intuition; repeat find_rewrite; eauto; eapply_prop_hyp pBody pBody; eauto; omega.
+
remember (pDst p0).
subst p0.
simpl in *.
subst.
find_copy_apply_lem_hyp handleRequestVote_reply_true'.
intuition.
subst.
eapply requestVote_term_sanity_invariant; eauto.
